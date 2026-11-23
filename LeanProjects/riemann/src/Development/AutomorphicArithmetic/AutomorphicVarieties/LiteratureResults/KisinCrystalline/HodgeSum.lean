import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KisinDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TypeDeformPer
open UpperTheory.V.Lit UpperTheory.V.Published

namespace UpperTheory.V.Lit.HodgeFiltrationSum

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct Module UpperTheory.V.Loc

section Lin

variable {Q W : Type} [Field Q] [AddCommGroup W] [Module Q W]

private theorem step {P : Type} [AddCommGroup P] [Module Q P] (F F' : Submodule Q W) [FiniteDimensional Q F]
    (hle : F' ≤ F) (Φ : P →ₗ[Q] W) (hΦ : ∀ c, Φ c ∈ F) (h : ∀ y ∈ F, ∃! c, y - Φ c ∈ F') :
    finrank Q F = finrank Q F' + finrank Q P := by
  have h0 : ∀ c, Φ c ∈ F' → c = 0 := fun c hc =>
    (h 0 F.zero_mem).unique (by simpa using hc) (by simp)
  have hinj : Function.Injective Φ := (injective_iff_map_eq_zero Φ).2 fun c hc => h0 c (hc ▸ F'.zero_mem)
  have hr : LinearMap.range Φ ≤ F := by
    rintro _ ⟨c, rfl⟩
    exact hΦ c
  have hsup : F' ⊔ LinearMap.range Φ = F := by
    refine le_antisymm (sup_le hle hr) fun y hy => ?_
    obtain ⟨c, hc, -⟩ := h y hy
    exact Submodule.mem_sup.2 ⟨_, hc, Φ c, ⟨c, rfl⟩, sub_add_cancel _ _⟩
  have hinf : F' ⊓ LinearMap.range Φ = ⊥ := by
    refine eq_bot_iff.2 ?_
    rintro _ ⟨hy, c, rfl⟩
    rw [h0 c hy, map_zero]
    exact Submodule.zero_mem _
  haveI := Submodule.finiteDimensional_of_le hle
  haveI := Submodule.finiteDimensional_of_le hr
  have := Submodule.finrank_sup_add_finrank_inf_eq F' (LinearMap.range Φ)
  rw [hsup, hinf, finrank_bot, add_zero, LinearMap.finrank_range_of_inj hinj] at this
  exact this

private theorem total (D : Submodule Q W) [FiniteDimensional Q D] (F : ℤ → Submodule Q W) (hF : Antitone F)
    (hD : ∀ i, F i ≤ D) (hex : ∀ y ∈ D, ∃ a, y ∈ F a) (hsep : ∀ y, (∀ a, y ∈ F a) → y = 0)
    (c n : ℕ) (hc : 0 < c) (m : ℤ → ℕ) (hm : ∀ i, finrank Q (F i) = finrank Q (F (i + 1)) + c * m i)
    (hn : finrank Q D = c * n) :
    ∃ (a : ℤ) (h : ℕ), (∀ i, i < a ∨ a + h < i → m i = 0) ∧ ∑ i ∈ Finset.range (h + 1), m (a + i) = n := by
  haveI : ∀ i, FiniteDimensional Q (F i) := fun i => Submodule.finiteDimensional_of_le (hD i)
  obtain ⟨b, hb⟩ : ∃ b, ∀ i, finrank Q (F b) ≤ finrank Q (F i) :=
    ⟨Function.argmin fun i => finrank Q (F i), fun i => Function.argmin_le (fun i => finrank Q (F i)) i⟩
  obtain ⟨a, ha⟩ : ∃ a, ∀ i, finrank Q D - finrank Q (F a) ≤ finrank Q D - finrank Q (F i) :=
    ⟨Function.argmin fun i => finrank Q D - finrank Q (F i),
      fun i => Function.argmin_le (fun i => finrank Q D - finrank Q (F i)) i⟩
  have ha1 : ∀ i ≤ a, F a = F i := fun i hi => by
    refine Submodule.eq_of_le_of_finrank_le (hF hi) ?_
    have h1 := ha i
    have h2 := Submodule.finrank_mono (hD i)
    have h3 := Submodule.finrank_mono (hD a)
    omega
  have hb1 : ∀ i, b ≤ i → F i = F b := fun i hi => Submodule.eq_of_le_of_finrank_le (hF hi) (hb i)
  have ha2 : F a = D := le_antisymm (hD a) fun y hy => by
    obtain ⟨j, hj⟩ := hex y hy
    rw [ha1 _ (min_le_left a j)]
    exact hF (min_le_right a j) hj
  have hb2 : F b = ⊥ := eq_bot_iff.2 fun y hy => hsep y fun j =>
    hF (le_max_right b j) (by rw [hb1 _ (le_max_left b j)]; exact hy)
  have ha3 : ∀ i ≤ a, finrank Q (F i) = c * n := fun i hi => by rw [← ha1 i hi, ha2, hn]
  have hb3 : ∀ i, b ≤ i → finrank Q (F i) = 0 := fun i hi => by rw [hb1 i hi, hb2, finrank_bot]
  have tel : ∀ k : ℕ, c * n = finrank Q (F (a + k)) + c * ∑ i ∈ Finset.range k, m (a + i) := by
    intro k
    induction k with
    | zero => rw [ha3 _ (by simp), Finset.sum_range_zero, mul_zero, add_zero]
    | succ k ih =>
      rw [Finset.sum_range_succ, mul_add, Nat.cast_succ, ← add_assoc a, ih, hm]
      ring
  refine ⟨a, (b - a).toNat, fun i hi => ?_, ?_⟩
  · have h1 := hm i
    have : c * m i = 0 := by
      rcases hi with hi | hi
      · rw [ha3 i hi.le, ha3 (i + 1) (by omega)] at h1
        omega
      · rw [hb3 i (by omega)] at h1
        omega
    exact (Nat.mul_eq_zero.1 this).resolve_left hc.ne'
  · have h1 := tel ((b - a).toNat + 1)
    rw [hb3 _ (by omega), zero_add] at h1
    exact (Nat.eq_of_mul_eq_mul_left hc h1).symm

private theorem sep {V : Type} [AddCommGroup V] [Module Q V] (F : ℤ → Submodule Q W)
    (hsep : ∀ y, (∀ a, y ∈ F a) → y = 0) (y : V ⊗[Q] W)
    (hy : ∀ a, ∃ z : V ⊗[Q] F a, LinearMap.lTensor V (F a).subtype z = y) : y = 0 := by
  classical
  let e := Basis.ofVectorSpace Q V
  apply (TensorProduct.equivFinsuppOfBasisLeft e).injective
  rw [map_zero]
  ext i
  refine hsep _ fun a => ?_
  obtain ⟨z, rfl⟩ := hy a
  clear hy
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, Finsupp.add_apply]; exact (F a).add_mem hx hy
  | tmul v b =>
    rw [LinearMap.lTensor_tmul, TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
    exact (F a).smul_mem _ b.2

end Lin

variable {l : ℕ} [Fact l.Prime] {A V : Type} [CommRing A] [Algebra ℚ_[l] A] [AddCommGroup V] [Module A V]
  [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V]

private theorem filT_anti : Antitone (FilT (l := l) A V) := antitone_int_of_succ_le fun a => by
  rintro _ ⟨y, rfl⟩
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | tmul v b => exact ⟨v ⊗ₜ ⟨b.1, ((PP l).PD (botExt l)).Fil_anti a b.2⟩, rfl⟩

private theorem filT_exh (y : V ⊗[ℚ_[l]] Bdr l) : ∃ a, y ∈ FilT A V a := by
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, Submodule.zero_mem _⟩
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨min a b, Submodule.add_mem _ (filT_anti (min_le_left a b) ha) (filT_anti (min_le_right a b) hb)⟩
  | tmul v b =>
    obtain ⟨a, ha⟩ := ((PP l).PD (botExt l)).Fil_exh b
    exact ⟨a, v ⊗ₜ ⟨b, ha⟩, rfl⟩

private theorem filT_sep (y : V ⊗[ℚ_[l]] Bdr l) (hy : ∀ a, y ∈ FilT A V a) : y = 0 :=
  sep (fun a => (((PP l).PD (botExt l)).Fil a).restrictScalars ℚ_[l]) ((PP l).PD (botExt l)).Fil_sep y hy

private theorem main [Nontrivial A] [Module.Finite ℚ_[l] A] [FiniteDimensional ℚ_[l] V] (K : FinExt l)
    (ρ : Representation A ↥(GK K) V) (n : ℕ) (hn : finrank ℚ_[l] V = finrank ℚ_[l] A * n) (hd : DeRham K ρ)
    (m : ℤ → ℕ) (hm : HodgeType K ρ m) :
    ∃ (a : ℤ) (h : ℕ), (∀ i, i < a ∨ a + h < i → m i = 0) ∧ ∑ i ∈ Finset.range (h + 1), m (a + i) = n := by
  haveI := K.2
  have hK : 0 < finrank ℚ_[l] ↥K.1 := finrank_pos
  have hA : 0 < finrank ℚ_[l] A := finrank_pos
  have hd' : finrank ℚ_[l] ↥(DdR ((PP l).PD K) (resCoef ℚ_[l] ρ)) = finrank ℚ_[l] ↥K.1 * finrank ℚ_[l] V := hd
  haveI : FiniteDimensional ℚ_[l] ↥(DdR ((PP l).PD K) (resCoef ℚ_[l] ρ)) := by
    rcases subsingleton_or_nontrivial V with h | h
    · infer_instance
    · exact Module.finite_of_finrank_pos (hd' ▸ Nat.mul_pos hK finrank_pos)
  have hle : ∀ i, (FilD (GK K).subtype ρ i).restrictScalars ℚ_[l] ≤ DdR ((PP l).PD K) (resCoef ℚ_[l] ρ) :=
    fun i y hy => ((Thick.mem_FilD_iff K ρ i y).1 hy).1
  refine total (DdR ((PP l).PD K) (resCoef ℚ_[l] ρ)) (fun i => (FilD (GK K).subtype ρ i).restrictScalars ℚ_[l])
    (fun i j hij y hy => ⟨hy.1, filT_anti hij hy.2⟩) hle (fun y hy => ?_)
    (fun y hy => filT_sep (A := A) y fun a => (hy a).2) (finrank ℚ_[l] A * finrank ℚ_[l] ↥K.1) n
    (Nat.mul_pos hA hK) m (fun i => ?_) (by rw [hd', hn]; ring)
  · obtain ⟨a, ha⟩ := filT_exh (A := ℚ_[l]) y
    refine ⟨a, (Thick.mem_FilD_iff K ρ a y).2 ⟨hy, ?_⟩⟩
    have : (((PP l).PD (botExt l)).Fil a).restrictScalars ℚ_[l] = (((PP l).PD K).Fil a).restrictScalars ℚ_[l] :=
      SetLike.coe_injective ((PP l).PD_Fil _ _ a)
    unfold FilT at ha
    rw [this] at ha
    exact ha
  · obtain ⟨x, hx, h⟩ := hm i
    haveI := Submodule.finiteDimensional_of_le (hle i)
    let Φ : (Fin (m i) → A ⊗[ℚ_[l]] ↥K.1) →ₗ[ℚ_[l]] V ⊗[ℚ_[l]] Bdr l :=
      { toFun := fun c => ∑ a, smulD V K (c a) (x a)
        map_add' := fun c c' => by simp only [Pi.add_apply, map_add, LinearMap.add_apply, Finset.sum_add_distrib]
        map_smul' := fun r c => by
          simp only [Pi.smul_apply, map_smul, LinearMap.smul_apply, RingHom.id_apply, Finset.smul_sum] }
    have := step ((FilD (GK K).subtype ρ i).restrictScalars ℚ_[l])
      ((FilD (GK K).subtype ρ (i + 1)).restrictScalars ℚ_[l]) (Thick.FilD_succ_le _ ρ i) Φ
      (fun c => show ∑ a, smulD V K (c a) (x a) ∈ FilD (GK K).subtype ρ i from
        Submodule.sum_mem _ fun a _ => Thick.smulD_mem K ρ _ i (hx a)) h
    rw [this, Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, finrank_tensorProduct,
      smul_eq_mul, mul_comm (m i)]

end UpperTheory.V.Lit.HodgeFiltrationSum
