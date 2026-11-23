import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Formalism.SharpRestriction.LevelLetterCocycles.AnnihilatorGeneralOfRingCondition
import Formalism.SharpRestriction.LevelLetterCocycles.LemmasUnramifiedOfRingCondition

noncomputable section

namespace Formalism.MainNotions.UnusedSlot80.LevR

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

section Laurent

variable {R M : Type} [Field R] [AddCommGroup M] [Module R M]

theorem finsum_mem_sub (S : Submodule R M) {g : ℕ → M} (hg : ∀ i, g i ∈ S) : ∑ᶠ i, g i ∈ S := by
  by_cases h : (Function.support g).Finite
  · rw [finsum_eq_sum_of_support_subset g (s := h.toFinset) (by simp)]
    exact Submodule.sum_mem _ fun i _ => hg i
  · rw [finsum_of_infinite_support h]
    exact S.zero_mem

theorem smul_finsum_mem (S : Submodule R M) (c : R) {g : ℕ → M} (hg : ∀ i, c • g i ∈ S) :
    c • ∑ᶠ i, g i ∈ S := by
  by_cases h : (Function.support g).Finite
  · rw [finsum_eq_sum_of_support_subset g (s := h.toFinset) (by simp), Finset.smul_sum]
    exact Submodule.sum_mem _ fun i _ => hg i
  · rw [finsum_of_infinite_support h, smul_zero]
    exact S.zero_mem

theorem smul_finsum_sub_mem (S : Submodule R M) (c : R) {g : ℕ → M} (hfin : (Function.support g).Finite)
    (w : M) (h0 : c • g 0 - w ∈ S) (hg : ∀ i, 1 ≤ i → c • g i ∈ S) : c • (∑ᶠ i, g i) - w ∈ S := by
  classical
  rw [finsum_eq_sum_of_support_subset g (s := insert 0 hfin.toFinset)
    (fun x hx => Finset.mem_coe.mpr (Finset.mem_insert_of_mem (hfin.mem_toFinset.mpr hx))),
    ← Finset.add_sum_erase _ g (Finset.mem_insert_self 0 _), smul_add, Finset.smul_sum]
  have hs : ∑ i ∈ (insert 0 hfin.toFinset).erase 0, c • g i ∈ S :=
    Submodule.sum_mem _ fun i hi => hg i (Nat.one_le_iff_ne_zero.mpr (Finset.ne_of_mem_erase hi))
  have e : c • g 0 + ∑ i ∈ (insert 0 hfin.toFinset).erase 0, c • g i - w =
      (c • g 0 - w) + ∑ i ∈ (insert 0 hfin.toFinset).erase 0, c • g i := by abel
  rw [e]
  exact S.add_mem h0 hs

theorem supp_fin {f : ℤ → M} {m : ℤ} (hm : ∀ k < m, f k = 0) (d : ℕ → M →ₗ[R] M) (k : ℤ) :
    (Function.support fun j : ℕ => d j (f (k - j))).Finite := by
  apply (Finset.range ((k - m).toNat + 1)).finite_toSet.subset
  intro j hj
  simp only [Function.mem_support] at hj
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra hc
  apply hj
  have h1 : (((k - m).toNat : ℕ) : ℤ) + 1 ≤ (j : ℤ) := by exact_mod_cast (not_lt.mp hc)
  have h2 := Int.self_le_toNat (k - m)
  rw [hm (k - j) (by omega), map_zero]

theorem laurent_mem (F : ℤ → Submodule R M) (hF : Monotone F) {f : ℤ → M} (hf : ∀ k, f k ∈ F k)
    (u : PowerSeries R) (k : ℤ) : ∑ᶠ j : ℕ, PowerSeries.coeff j u • f (k - j) ∈ F k :=
  finsum_mem_sub _ fun j => (F k).smul_mem _ (hF (by omega) (hf (k - j)))

theorem laurent_div (F : ℤ → Submodule R M) (hF : Monotone F) {f : ℤ → M} {m : ℤ}
    (hm : ∀ k < m, f k = 0) (u : PowerSeries R) (hu : PowerSeries.constantCoeff u ≠ 0)
    (hg : ∀ k, ∑ᶠ j : ℕ, PowerSeries.coeff j u • f (k - j) ∈ F k) : ∀ k, f k ∈ F k := by
  have key : ∀ N : ℕ, ∀ k, k < m + N → f k ∈ F k := by
    intro N
    induction N with
    | zero => intro k hk; rw [hm k (by omega)]; exact (F k).zero_mem
    | succ N ih =>
      intro k hk
      have hfin := supp_fin hm (fun j : ℕ => (PowerSeries.coeff j u • LinearMap.id : M →ₗ[R] M)) k
      have h1 := smul_finsum_sub_mem (F k) (1 : R) hfin (PowerSeries.coeff 0 u • f k)
        (by simp) (fun i hi => by
          simp only [LinearMap.smul_apply, LinearMap.id_apply, one_smul]
          exact (F k).smul_mem _ (hF (by omega) (ih (k - i) (by omega))))
      simp only [LinearMap.smul_apply, LinearMap.id_apply, one_smul] at h1
      have h2 : PowerSeries.coeff 0 u • f k ∈ F k := by
        have := (F k).sub_mem (hg k) h1
        rwa [sub_sub_cancel] at this
      have hu' : PowerSeries.coeff 0 u ≠ 0 := by
        rwa [PowerSeries.coeff_zero_eq_constantCoeff_apply]
      have := (F k).smul_mem (PowerSeries.coeff 0 u)⁻¹ h2
      rwa [smul_smul, inv_mul_cancel₀ hu', one_smul] at this
  intro k
  have h2 := Int.self_le_toNat (k - m)
  exact key ((k - m).toNat + 1) k (by push_cast; omega)

end Laurent

section Fil

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem fil_anti : Antitone PD.Fil := antitone_int_of_succ_le PD.Fil_anti

theorem filV_anti : Antitone (FilV PD (LL := LL) (V := V)) := by
  intro a b hab
  have hle : (PD.Fil b).restrictScalars Qp ≤ (PD.Fil a).restrictScalars Qp := fil_anti hab
  unfold FilV
  rw [← Submodule.subtype_comp_inclusion _ _ hle, ← LinearMap.id_comp (LinearMap.id : V →ₗ[LL] V),
    TensorProduct.AlgebraTensorModule.map_comp]
  exact LinearMap.range_comp_le_range _ _

variable (ρ : Representation LL G V)

theorem filCris_anti : Antitone (FilCris PD ρ) := fun _ _ hab =>
  inf_le_inf_left _ (Submodule.comap_mono (filV_anti hab))

theorem ιV_inj : Function.Injective (ιV PD (LL := LL) (V := V)) := by
  have h : ∀ y, ιV PD (LL := LL) (V := V) y =
      ((PD.ι.toLinearMap.restrictScalars Qp).lTensor V) y := fun y => by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul x b => simp [ιV]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hi : Function.Injective (PD.ι.toLinearMap.restrictScalars Qp) := PD.ι_inj
  intro a b hab
  rw [h, h] at hab
  exact Module.Flat.lTensor_preserves_injective_linearMap _ hi hab

theorem mem_of_map_ιV {S : Submodule LL (V ⊗[Qp] B)} {z : V ⊗[Qp] B}
    (h : ιV PD (LL := LL) (V := V) z ∈ S.map (ιV PD (LL := LL) (V := V))) : z ∈ S := by
  obtain ⟨y, hy, e⟩ := h
  rwa [ιV_inj e] at hy

theorem ιV_act (g : G) (y : V ⊗[Qp] B) :
    ιV PD (LL := LL) (V := V) (actVB PD ρ g y) = actVdR PD ρ g (ιV PD (LL := LL) (V := V) y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul x b => simp [ιV, actVB, actVdR, PD.ι_comm]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem ιV_mul (c : K₀) (y : V ⊗[Qp] B) :
    ιV PD (LL := LL) (V := V) (mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c y) =
      mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) (algebraMap K₀ K c)
        (ιV PD (LL := LL) (V := V) y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul x b =>
    simp [ιV, mulVB, mulVdR, ← IsScalarTower.algebraMap_apply K₀ K BdR]
  | add x y hx hy => simp only [map_add, hx, hy]

end Fil

section W

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

def Phi (T : LocLat G Qp LL O) (s : ℕ) (u : ℤ) (c : ZMod n) : Submodule LL (T.V ⊗[Qp] B) :=
  (FilCris PD T.ρ u ⊓ DcrisL PD T.ρ (W.emb c)).map
    ((φVB PD (LL := LL) (V := T.V) : Module.End LL (T.V ⊗[Qp] B)) ^ s)

theorem filLev_eq (T : LocLat G Qp LL O) (c : ZMod n) (s : ℕ) (u : ℤ) :
    Formalism.MainNotions.WachCoordinates.FilLev W T c s u = (Phi W T s u (c - (s : ZMod n))).map (ιV PD (LL := LL) (V := T.V)) :=
  rfl

theorem phi_anti (T : LocLat G Qp LL O) (s : ℕ) (c : ZMod n) : Antitone fun u => Phi W T s u c :=
  fun _ _ hab => Submodule.map_mono (inf_le_inf_right _ (filCris_anti T.ρ hab))

theorem filLev_anti (T : LocLat G Qp LL O) (c : ZMod n) (s : ℕ) :
    Antitone fun u => Formalism.MainNotions.WachCoordinates.FilLev W T c s u :=
  fun _ _ hab => Submodule.map_mono (phi_anti W T s _ hab)

theorem phi_succ (T : LocLat G Qp LL O) (s : ℕ) (u : ℤ) (c : ZMod n) {z : T.V ⊗[Qp] B}
    (hz : z ∈ Phi W T s u c) : φVB PD (LL := LL) (V := T.V) z ∈ Phi W T (s + 1) u c := by
  unfold Phi at hz ⊢
  rw [pow_succ', Module.End.mul_eq_comp, Submodule.map_comp]
  exact Submodule.mem_map_of_mem hz

theorem filLev_zero (T : LocLat G Qp LL O) (c : ZMod n) (u : ℤ) :
    Formalism.MainNotions.WachCoordinates.FilLev W T c 0 u = Formalism.MainNotions.DeltaInvariantLattices.ιDi W T c ⊓ FilV PD (LL := LL) (V := T.V) u := by
  rw [filLev_eq]
  unfold Phi Formalism.MainNotions.DeltaInvariantLattices.ιDi
  simp only [Nat.cast_zero, sub_zero, pow_zero, Module.End.one_eq_id, Submodule.map_id]
  ext x
  simp only [Submodule.mem_map, Submodule.mem_inf, FilCris, Submodule.mem_comap]
  constructor
  · rintro ⟨y, ⟨⟨-, hy⟩, hyc⟩, rfl⟩
    exact ⟨⟨y, hyc, rfl⟩, hy⟩
  · rintro ⟨⟨y, hyc, rfl⟩, hy⟩
    exact ⟨y, ⟨⟨(Submodule.mem_inf.mp hyc).1, hy⟩, hyc⟩, rfl⟩

theorem lev_letE (c : ZMod n) (ζ : LL) : W.lev c ζ (letE c : LetA O n) = 1 := by
  have h : W.lev c ζ (1 - letE c) = 0 := W.lev_letter c ζ _ (by simp [letE])
  rw [map_sub, map_one, sub_eq_zero] at h
  exact h.symm

theorem levN_letE (T : LocLat G Qp LL O) (c : ZMod n) (ζ : LL) (x : ↥(W.N T)) (k : ℤ) :
    W.levN T c ζ ((letE c : LetA O n) • x) k = W.levN T c ζ x k := by
  rw [W.levN_smul, lev_letE,
    finsum_eq_single _ 0 (fun j hj => by rw [PowerSeries.coeff_one, if_neg hj, zero_smul])]
  simp

end W

end Formalism.MainNotions.UnusedSlot80.LevR

namespace Formalism.MainNotions.UnusedSlot80.LevR

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

section Sep

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem eig_of_DdRE {τ : K →ₐ[Qp] LL} {e : V ⊗[Qp] BdR} (he : e ∈ DdRE PD ρ τ) (c : K) :
    mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) c e = τ c • e := by
  have h := (Submodule.mem_iInf _).mp (Submodule.mem_inf.mp he).2 c
  simpa only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    sub_eq_zero] using h

theorem localization_quotient_separated_dvd (τ : K →ₐ[Qp] LL) (P : (K →ₐ[Qp] LL) → Submodule LL (V ⊗[Qp] BdR))
    (hP : ∀ τ' e, e ∈ P τ' → ∀ c : K, mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) c e = τ' c • e)
    (hPτ : P τ = ⊥) (F : Submodule LL (V ⊗[Qp] BdR))
    (hF : ∀ f ∈ F, ∀ c : K, mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) c f = τ c • f)
    (S : Finset (K →ₐ[Qp] LL)) :
    ∀ d f e, (∀ c : K, mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) c d = τ c • d) → f ∈ F →
      e ∈ ⨆ τ' ∈ S, P τ' → d = f + e → d ∈ F := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro d f e _ hf he hd
    simp only [Finset.notMem_empty, iSup_false, iSup_bot, Submodule.mem_bot] at he
    rw [hd, he, add_zero]
    exact hf
  | @insert τ₁ S _ ih =>
    intro d f e hd hf he hde
    rw [Finset.iSup_insert, Submodule.mem_sup] at he
    obtain ⟨e₁, he₁, e', he', rfl⟩ := he
    by_cases h1 : τ₁ = τ
    · subst h1
      rw [hPτ, Submodule.mem_bot] at he₁
      subst he₁
      exact ih d f e' hd hf he' (by rw [hde, zero_add])
    · obtain ⟨c, hc⟩ : ∃ c, τ₁ c ≠ τ c := by
        by_contra hcon
        push Not at hcon
        exact h1 (AlgHom.ext hcon)
      set A := mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) c -
        τ₁ c • (LinearMap.id : V ⊗[Qp] BdR →ₗ[LL] V ⊗[Qp] BdR) with hA
      have hl : τ c - τ₁ c ≠ 0 := sub_ne_zero.mpr (Ne.symm hc)
      have hAS : A e' ∈ ⨆ τ' ∈ S, P τ' := by
        have hle : (⨆ τ' ∈ S, P τ').map A ≤ ⨆ τ' ∈ S, P τ' := by
          simp only [Submodule.map_iSup]
          exact iSup₂_mono fun τ' _ => Submodule.map_le_iff_le_comap.mpr fun e he => by
            simp only [Submodule.mem_comap, hA, LinearMap.sub_apply, LinearMap.smul_apply,
              LinearMap.id_apply, hP τ' e he c, ← sub_smul]
            exact (P τ').smul_mem _ he
        exact hle (Submodule.mem_map_of_mem he')
      have hAd : A d = (τ c - τ₁ c) • d := by
        simp only [hA, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hd c, sub_smul]
      have hAf : A f = (τ c - τ₁ c) • f := by
        simp only [hA, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hF f hf c,
          sub_smul]
      have hAe : A e₁ = 0 := by
        simp only [hA, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hP τ₁ e₁ he₁ c,
          sub_self]
      have key : (τ c - τ₁ c) • d = (τ c - τ₁ c) • f + A e' := by
        rw [← hAd, ← hAf, hde, map_add, map_add, hAe, zero_add]
      have hd' := ih ((τ c - τ₁ c) • d) ((τ c - τ₁ c) • f) (A e')
        (fun c' => by rw [map_smul, hd c', smul_comm]) (F.smul_mem _ hf) hAS key
      have := F.smul_mem (τ c - τ₁ c)⁻¹ hd'
      rwa [smul_smul, inv_mul_cancel₀ hl, one_smul] at this

theorem dR_sep (τ : K →ₐ[Qp] LL) (a : ℤ) :
    DdRE PD ρ τ ⊓ (FildR PD ρ τ a ⊔ ⨆ (τ' : K →ₐ[Qp] LL) (_ : τ' ≠ τ), DdRE PD ρ τ') ≤
      FilV PD (LL := LL) (V := V) a := by
  intro d hd
  obtain ⟨hdE, hdC⟩ := Submodule.mem_inf.mp hd
  obtain ⟨f, hf, e, he, rfl⟩ := Submodule.mem_sup.mp hdC
  obtain ⟨S, hS⟩ := Submodule.mem_iSup_iff_exists_finset.mp he
  have hP : ∀ τ' e, e ∈ (⨆ (_ : τ' ≠ τ), DdRE PD ρ τ') → ∀ c : K,
      mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) c e = τ' c • e := by
    intro τ' e he c
    by_cases h : τ' ≠ τ
    · rw [iSup_pos h] at he
      exact eig_of_DdRE ρ he c
    · rw [iSup_neg h, Submodule.mem_bot] at he
      subst he
      simp
  have := localization_quotient_separated_dvd τ (fun τ' => ⨆ (_ : τ' ≠ τ), DdRE PD ρ τ') hP (by simp) (FildR PD ρ τ a)
    (fun f hf c => eig_of_DdRE ρ (Submodule.mem_inf.mp hf).1 c) S (f + e) f e (eig_of_DdRE ρ hdE) hf hS rfl
  exact (Submodule.mem_inf.mp this).2

end Sep

section W

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

def Lv1 (T : LocLat G Qp LL O) (c : ZMod n) (s : ℕ) (ζ : LL) : Prop :=
  ∀ (x : ↥(W.N T)) (k : ℤ), W.levN T c ζ x k ∈ Formalism.MainNotions.WachCoordinates.FilLev W T c s (-k)

def Lv2 (T : LocLat G Qp LL O) (c : ZMod n) (s : ℕ) (ζ : LL) : Prop :=
  ∀ (k : ℤ), ∀ w ∈ Formalism.MainNotions.WachCoordinates.FilLev W T c s (-k), ∃ (x : ↥(W.N T)) (a : LL), a ≠ 0 ∧
    (∀ j < k, a • W.levN T c ζ x j ∈ Formalism.MainNotions.WachCoordinates.FilLev W T c s (-j + 1)) ∧
    a • W.levN T c ζ x k - w ∈ Formalism.MainNotions.WachCoordinates.FilLev W T c s (-k + 1)

theorem level_condition_of_all_levels (h : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ (c : ZMod n) (s : ℕ) (ζ : LL),
    IsPrimitiveRoot ζ (PD.p ^ (s + 1)) → Lv1 W T c s ζ ∧ Lv2 W T c s ζ) : Formalism.MainNotions.WachCoordinates.LevelMapHodgeFiltration W := h

theorem ιDi_le (T : LocLat G Qp LL O) (c : ZMod n) (τ : K →ₐ[Qp] LL)
    (hover : ∀ x : K₀, τ (algebraMap K₀ K x) = W.emb c x)
    (hsurj : Function.Surjective (algebraMap K₀ K)) : Formalism.MainNotions.DeltaInvariantLattices.ιDi W T c ≤ DdRE PD T.ρ τ := by
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨hyD, hyL⟩ := Submodule.mem_inf.mp hy
  refine Submodule.mem_inf.mpr ⟨(Submodule.mem_iInf _).mpr fun g => ?_,
    (Submodule.mem_iInf _).mpr fun c' => ?_⟩
  · have h := (Submodule.mem_iInf _).mp hyD g
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at h ⊢
    rw [← ιV_act, h]
  · obtain ⟨c₀, rfl⟩ := hsurj c'
    have h := (Submodule.mem_iInf _).mp hyL c₀
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      sub_eq_zero] at h ⊢
    rw [← ιV_mul, h, map_smul, hover]

theorem lev0 (T : LocLat G Qp LL O) (c : ZMod n) (ζ : LL) (τ : K →ₐ[Qp] LL)
    (hτ : Formalism.MainNotions.DeltaInvariantLattices.ιDi W T c ≤ DdRE PD T.ρ τ)
    (h4 : (∀ (x : ↥(W.N T)) (k : ℤ), W.levN T c ζ ((letE c : LetA O n) • x) k ∈
        Formalism.MainNotions.DeltaInvariantLattices.ιDi W T c ⊓ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (-k)) ∧
      ∀ (k : ℤ), ∀ w ∈ FildR PD T.ρ τ (-k), ∃ (x : ↥(W.N T)) (a : LL), a ≠ 0 ∧
        (∀ j < k, a • W.levN T c ζ ((letE c : LetA O n) • x) j ∈
          Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (-j + 1)) ∧
        a • W.levN T c ζ ((letE c : LetA O n) • x) k - w ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (-k + 1)) :
    Lv1 W T c 0 ζ ∧ Lv2 W T c 0 ζ := by
  have sep : ∀ (a : ℤ) z, z ∈ Formalism.MainNotions.DeltaInvariantLattices.ιDi W T c → z ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ a →
      z ∈ Formalism.MainNotions.WachCoordinates.FilLev W T c 0 a := by
    intro a z hz hC
    rw [filLev_zero]
    exact Submodule.mem_inf.mpr ⟨hz, dR_sep T.ρ τ a (Submodule.mem_inf.mpr ⟨hτ hz, hC⟩)⟩
  refine ⟨fun x k => ?_, fun k w hw => ?_⟩
  · rw [← levN_letE]
    obtain ⟨h1, h2⟩ := Submodule.mem_inf.mp (h4.1 x k)
    exact sep _ _ h1 h2
  · rw [filLev_zero] at hw
    obtain ⟨hwD, hwF⟩ := Submodule.mem_inf.mp hw
    obtain ⟨x, a, ha, hj, hk⟩ := h4.2 k w (Submodule.mem_inf.mpr ⟨hτ hwD, hwF⟩)
    have hD : ∀ j, W.levN T c ζ ((letE c : LetA O n) • x) j ∈ Formalism.MainNotions.DeltaInvariantLattices.ιDi W T c :=
      fun j => (Submodule.mem_inf.mp (h4.1 x j)).1
    exact ⟨(letE c : LetA O n) • x, a, ha,
      fun j hj' => sep _ _ ((Formalism.MainNotions.DeltaInvariantLattices.ιDi W T c).smul_mem a (hD j)) (hj j hj'),
      sep _ _ ((Formalism.MainNotions.DeltaInvariantLattices.ιDi W T c).sub_mem ((Formalism.MainNotions.DeltaInvariantLattices.ιDi W T c).smul_mem a (hD k)) hwD) hk⟩

end W

end Formalism.MainNotions.UnusedSlot80.LevR

namespace Formalism.MainNotions.UnusedSlot80.LevR

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

section W

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)
    (levB : ∀ T : LocLat G Qp LL O, ZMod n → LL → ↥(W.N T) →+ (ℤ → T.V ⊗[Qp] B))

def LevBφ : Prop :=
  ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ (i : ZMod n) (ζ : LL),
    (∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) → ∀ (x : ↥(W.N T)) (m : ℕ)
    (hx : W.Q ^ m • W.φD T (x : W.DD T) ∈ W.N T) (k : ℤ),
    levB T i ζ ⟨W.Q ^ m • W.φD T (x : W.DD T), hx⟩ k =
      ∑ᶠ j : ℕ, PowerSeries.coeff j (W.lev i ζ (W.Q ^ m)) •
        (((PD.p : LL) ^ (k - (j : ℤ))) •
          φVB PD (LL := LL) (V := T.V) (levB T (i - 1) (ζ ^ PD.p) x (k - (j : ℤ))))

theorem transport
    (hEq : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (x : ↥(W.N T)) (k : ℤ),
      W.levN T i ζ x k = ιV PD (LL := LL) (V := T.V) (levB T i ζ x k))
    (hφ : LevBφ W levB) (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (c : ZMod n) (s : ℕ) (ζ : LL)
    (hζ : ∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j))
    (hQ : PowerSeries.constantCoeff (W.lev c ζ W.Q) ≠ 0) (hp : (PD.p : LL) ≠ 0)
    (ih1 : Lv1 W T (c - 1) s (ζ ^ PD.p)) (ih2 : Lv2 W T (c - 1) s (ζ ^ PD.p)) :
    Lv1 W T c (s + 1) ζ ∧ Lv2 W T c (s + 1) ζ := by
  set c' : ZMod n := c - ((s + 1 : ℕ) : ZMod n) with hc'
  have hcc : c - 1 - (s : ZMod n) = c' := by rw [hc']; push_cast; ring
  have hB1 : ∀ (y : ↥(W.N T)) (k : ℤ), levB T (c - 1) (ζ ^ PD.p) y k ∈ Phi W T s (-k) c' := by
    intro y k
    have h := ih1 y k
    rw [filLev_eq, hEq, hcc] at h
    exact mem_of_map_ιV h
  have hX : ∀ (y : ↥(W.N T)) (m : ℕ) (hx : W.Q ^ m • W.φD T (y : W.DD T) ∈ W.N T) (k : ℤ),
      levB T c ζ ⟨_, hx⟩ k ∈ Phi W T (s + 1) (-k) c' := by
    intro y m hx k
    rw [hφ T hT c ζ hζ y m hx k]
    refine finsum_mem_sub _ fun j => Submodule.smul_mem _ _ (Submodule.smul_mem _ _ ?_)
    exact phi_anti W T (s + 1) c' (by omega : -k ≤ -(k - (j : ℤ))) (phi_succ W T s _ c' (hB1 y _))
  set F : ℤ → Submodule LL (T.V ⊗[Qp] BdR) := fun k => Formalism.MainNotions.WachCoordinates.FilLev W T c (s + 1) (-k) with hF
  have hFm : Monotone F := fun a b hab => filLev_anti W T c (s + 1) (by omega : -b ≤ -a)
  let Good : ↥(W.N T) → Prop := fun x => ∀ k, W.levN T c ζ x k ∈ F k
  have gX : ∀ (y : ↥(W.N T)) (m : ℕ) (hx : W.Q ^ m • W.φD T (y : W.DD T) ∈ W.N T),
      Good ⟨_, hx⟩ := fun y m hx k => by
    show W.levN T c ζ _ k ∈ Formalism.MainNotions.WachCoordinates.FilLev W T c (s + 1) (-k)
    rw [hEq, filLev_eq]
    exact Submodule.mem_map_of_mem (hX y m hx k)
  have gS : ∀ (a : LetA O n) (x : ↥(W.N T)), Good x → Good (a • x) := fun a x hx k => by
    show W.levN T c ζ (a • x) k ∈ F k
    rw [W.levN_smul]
    exact laurent_mem F hFm hx _ k
  have gA : ∀ x y : ↥(W.N T), Good x → Good y → Good (x + y) := fun x y hx hy k => by
    show W.levN T c ζ (x + y) k ∈ F k
    rw [map_add, Pi.add_apply]
    exact (F k).add_mem (hx k) (hy k)
  have g0 : Good 0 := fun k => by
    show W.levN T c ζ 0 k ∈ F k
    rw [map_zero, Pi.zero_apply]
    exact (F k).zero_mem
  have gD : ∀ (a : LetA O n) (x : ↥(W.N T)), PowerSeries.constantCoeff (W.lev c ζ a) ≠ 0 →
      Good (a • x) → Good x := by
    intro a x ha hx
    obtain ⟨m, hm⟩ := W.levN_supp T c ζ x
    exact laurent_div F hFm hm (W.lev c ζ a) ha (fun k => by
      have := hx k
      rwa [W.levN_smul] at this)
  let GoodD : W.DD T → Prop := fun z => ∃ h : z ∈ W.N T, Good ⟨z, h⟩
  have dS : ∀ (a : LetA O n) (z : W.DD T), GoodD z → GoodD (a • z) := fun a z ⟨h, hz⟩ =>
    ⟨(W.N T).smul_mem a h, gS a ⟨z, h⟩ hz⟩
  have dA : ∀ z1 z2 : W.DD T, GoodD z1 → GoodD z2 → GoodD (z1 + z2) :=
    fun z1 z2 ⟨h1, g1⟩ ⟨h2, g2⟩ => ⟨(W.N T).add_mem h1 h2, gA _ _ g1 g2⟩
  have hspan : ∀ z ∈ Submodule.span (LetA O n) (W.φD T '' (W.N T : Set (W.DD T))),
      ∃ M : ℕ, GoodD (W.Q ^ M • z) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨y, hy, rfl⟩ := hz
      obtain ⟨m, hm⟩ := W.N_φ T y hy
      exact ⟨m, hm, gX ⟨y, hy⟩ m hm⟩
    | zero => exact ⟨0, by rw [smul_zero]; exact ⟨(W.N T).zero_mem, g0⟩⟩
    | add z1 z2 _ _ h1 h2 =>
      obtain ⟨M1, g1⟩ := h1
      obtain ⟨M2, g2⟩ := h2
      refine ⟨M1 + M2, ?_⟩
      have e : W.Q ^ (M1 + M2) • (z1 + z2) =
          W.Q ^ M2 • (W.Q ^ M1 • z1) + W.Q ^ M1 • (W.Q ^ M2 • z2) := by
        rw [smul_add, smul_smul, smul_smul, ← pow_add, ← pow_add, add_comm M2 M1]
      rw [e]
      exact dA _ _ (dS _ _ g1) (dS _ _ g2)
    | smul a z _ h =>
      obtain ⟨M, g⟩ := h
      exact ⟨M, by rw [smul_comm]; exact dS a _ g⟩
  have L1 : Lv1 W T c (s + 1) ζ := by
    intro x k
    obtain ⟨K', hK'⟩ := W.N_φinv T x x.2
    obtain ⟨M, hM, gM⟩ := hspan _ hK'
    have hxeq : (⟨_, hM⟩ : ↥(W.N T)) = W.Q ^ (M + K') • x :=
      Subtype.ext (by rw [Submodule.coe_smul, pow_add, mul_smul]; rfl)
    rw [hxeq] at gM
    exact gD _ x (by rw [map_pow, map_pow]; exact pow_ne_zero _ hQ) gM k
  refine ⟨L1, fun k w hw => ?_⟩
  rw [filLev_eq] at hw
  obtain ⟨z, hz, rfl⟩ := hw
  obtain ⟨b, hb, rfl⟩ := hz
  have hw' : ιV PD (LL := LL) (V := T.V)
      (((φVB PD (LL := LL) (V := T.V) : Module.End LL (T.V ⊗[Qp] B)) ^ s) b) ∈
      Formalism.MainNotions.WachCoordinates.FilLev W T (c - 1) s (-k) := by
    rw [filLev_eq, hcc]
    exact Submodule.mem_map_of_mem (Submodule.mem_map_of_mem hb)
  obtain ⟨y, a, ha, hj, hk⟩ := ih2 k _ hw'
  have hj' : ∀ j < k, a • levB T (c - 1) (ζ ^ PD.p) y j ∈ Phi W T s (-j + 1) c' := by
    intro j hjk
    have h := hj j hjk
    rw [filLev_eq, hEq, ← map_smul, hcc] at h
    exact mem_of_map_ιV h
  have hk' : a • levB T (c - 1) (ζ ^ PD.p) y k -
      ((φVB PD (LL := LL) (V := T.V) : Module.End LL (T.V ⊗[Qp] B)) ^ s) b ∈ Phi W T s (-k + 1) c' := by
    have h := hk
    rw [filLev_eq, hEq, ← map_smul, ← map_sub, hcc] at h
    exact mem_of_map_ιV h
  obtain ⟨m, hm0φ⟩ := W.N_φ T y y.2
  have hm : W.Q ^ m • W.φD T (y : W.DD T) ∈ W.N T := hm0φ
  have hU : PowerSeries.coeff 0 (W.lev c ζ (W.Q ^ m)) ≠ 0 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, map_pow]
    exact pow_ne_zero _ hQ
  have hlam : PowerSeries.coeff 0 (W.lev c ζ (W.Q ^ m)) * (PD.p : LL) ^ k ≠ 0 :=
    mul_ne_zero hU (zpow_ne_zero _ hp)
  obtain ⟨m0, hm0⟩ := W.levN_supp T (c - 1) (ζ ^ PD.p) y
  have hm0' : ∀ k' < m0, levB T (c - 1) (ζ ^ PD.p) y k' = 0 := fun k' hk' =>
    ιV_inj (by rw [← hEq, hm0 k' hk', map_zero])
  have hexp := hφ T hT c ζ hζ y m hm
  refine ⟨⟨_, hm⟩, (PowerSeries.coeff 0 (W.lev c ζ (W.Q ^ m)) * (PD.p : LL) ^ k)⁻¹ * a,
    mul_ne_zero (inv_ne_zero hlam) ha, fun j hjk => ?_, ?_⟩
  · rw [hEq, filLev_eq, ← map_smul]
    apply Submodule.mem_map_of_mem
    rw [hexp, mul_smul]
    apply Submodule.smul_mem
    apply smul_finsum_mem
    intro i
    rw [smul_comm a, smul_comm a, ← LinearMap.map_smul]
    refine Submodule.smul_mem _ _ (Submodule.smul_mem _ _ ?_)
    exact phi_anti W T (s + 1) c' (by omega : -j + 1 ≤ -(j - (i : ℤ)) + 1)
      (phi_succ W T s _ c' (hj' _ (by omega)))
  · rw [hEq, filLev_eq, ← map_smul, ← map_sub]
    apply Submodule.mem_map_of_mem
    have e : ((PowerSeries.coeff 0 (W.lev c ζ (W.Q ^ m)) * (PD.p : LL) ^ k)⁻¹ * a) •
        levB T c ζ ⟨_, hm⟩ k -
          ((φVB PD (LL := LL) (V := T.V) : Module.End LL (T.V ⊗[Qp] B)) ^ (s + 1)) b =
        (PowerSeries.coeff 0 (W.lev c ζ (W.Q ^ m)) * (PD.p : LL) ^ k)⁻¹ •
          (a • levB T c ζ ⟨_, hm⟩ k - (PowerSeries.coeff 0 (W.lev c ζ (W.Q ^ m)) * (PD.p : LL) ^ k) •
            ((φVB PD (LL := LL) (V := T.V) : Module.End LL (T.V ⊗[Qp] B)) ^ (s + 1)) b) := by
      rw [smul_sub, smul_smul, smul_smul, inv_mul_cancel₀ hlam, one_smul]
    rw [e]
    apply Submodule.smul_mem
    rw [hexp]
    have hfin : (Function.support fun i : ℕ => PowerSeries.coeff i (W.lev c ζ (W.Q ^ m)) •
        (((PD.p : LL) ^ (k - (i : ℤ))) •
          φVB PD (LL := LL) (V := T.V) (levB T (c - 1) (ζ ^ PD.p) y (k - (i : ℤ))))).Finite :=
      (supp_fin hm0' (fun i : ℕ => PowerSeries.coeff i (W.lev c ζ (W.Q ^ m)) •
        ((PD.p : LL) ^ (k - (i : ℤ))) • (φVB PD (LL := LL) (V := T.V))) k).subset
        (fun i hi => by simpa only [Function.mem_support, LinearMap.smul_apply] using hi)
    refine smul_finsum_sub_mem _ a hfin _ ?_ ?_
    · have e0 : a • (PowerSeries.coeff 0 (W.lev c ζ (W.Q ^ m)) • (((PD.p : LL) ^ (k - ((0 : ℕ) : ℤ))) •
          φVB PD (LL := LL) (V := T.V) (levB T (c - 1) (ζ ^ PD.p) y (k - ((0 : ℕ) : ℤ))))) -
          (PowerSeries.coeff 0 (W.lev c ζ (W.Q ^ m)) * (PD.p : LL) ^ k) •
            ((φVB PD (LL := LL) (V := T.V) : Module.End LL (T.V ⊗[Qp] B)) ^ (s + 1)) b =
          (PowerSeries.coeff 0 (W.lev c ζ (W.Q ^ m)) * (PD.p : LL) ^ k) •
            φVB PD (LL := LL) (V := T.V) (a • levB T (c - 1) (ζ ^ PD.p) y k -
              ((φVB PD (LL := LL) (V := T.V) : Module.End LL (T.V ⊗[Qp] B)) ^ s) b) := by
        rw [Nat.cast_zero, sub_zero, map_sub, map_smul, pow_succ', Module.End.mul_apply]
        module
      rw [e0]
      exact Submodule.smul_mem _ _ (phi_succ W T s _ c' hk')
    · intro i hi
      rw [smul_comm a, smul_comm a, ← LinearMap.map_smul]
      refine Submodule.smul_mem _ _ (Submodule.smul_mem _ _ ?_)
      exact phi_anti W T (s + 1) c' (by omega : -k + 1 ≤ -(k - (i : ℤ)) + 1)
        (phi_succ W T s _ c' (hj' _ (by omega)))

theorem cc_lev_q (c : ZMod n) (ζ : LL) (hζ : ∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j))
    (hp1 : ζ ^ PD.p ≠ 1) : PowerSeries.constantCoeff (W.lev c ζ W.q) ≠ 0 := by
  obtain ⟨E, hE0, -, hE⟩ := W.lev_π c ζ hζ
  have hq : (letπ : LetA O n) * W.q = (1 + letπ) ^ PD.p - 1 := by
    funext i
    simp only [Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, Pi.add_apply, Pi.one_apply, letπ,
      LocWach.q, W.q₀_def]
  have h := congrArg (fun a => PowerSeries.constantCoeff (W.lev c ζ a)) hq
  simp only [map_mul, map_sub, map_pow, map_add, map_one] at h
  have hπ : PowerSeries.constantCoeff (W.lev c ζ letπ) = ζ - 1 := by
    have := congrArg PowerSeries.constantCoeff hE
    rw [map_add, map_one, map_mul, PowerSeries.constantCoeff_C, hE0, mul_one] at this
    linear_combination this
  intro h0
  rw [hπ, h0, mul_zero] at h
  apply hp1
  have e : (1 : LL) + (ζ - 1) = ζ := by ring
  rw [e] at h
  exact (sub_eq_zero.mp h.symm)

theorem level_condition_of_level_zero (hs : W.s = 1)
    (hEq : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (x : ↥(W.N T)) (k : ℤ),
      W.levN T i ζ x k = ιV PD (LL := LL) (V := T.V) (levB T i ζ x k))
    (hφ : LevBφ W levB) (hp : (PD.p : LL) ≠ 0)
    (h0 : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ (c : ZMod n) (ζ : LL),
      IsPrimitiveRoot ζ PD.p → Lv1 W T c 0 ζ ∧ Lv2 W T c 0 ζ) : Formalism.MainNotions.WachCoordinates.LevelMapHodgeFiltration W := by
  have hQq : W.Q = W.q := by simp [LocWach.Q, hs]
  apply level_condition_of_all_levels
  intro T hT c s
  induction s generalizing c with
  | zero => intro ζ hζ; exact h0 T hT c ζ (by simpa using hζ)
  | succ s ih =>
    intro ζ hζ
    have hp0 : 0 < PD.p ^ (s + 1 + 1) := pow_pos PD.hp.pos _
    have hζp : IsPrimitiveRoot (ζ ^ PD.p) (PD.p ^ (s + 1)) := hζ.pow hp0 (by ring)
    have hp1 : ζ ^ PD.p ≠ 1 := by
      intro h1
      have := hζ.pow_eq_one_iff_dvd PD.p
      rw [this] at h1
      have h2 := Nat.le_of_dvd PD.hp.pos h1
      have h3 : PD.p < PD.p ^ (s + 1 + 1) := by
        calc PD.p = PD.p ^ 1 := (pow_one _).symm
          _ < PD.p ^ (s + 1 + 1) := Nat.pow_lt_pow_right PD.hp.one_lt (by omega)
      omega
    obtain ⟨i1, i2⟩ := ih (c - 1) (ζ ^ PD.p) hζp
    exact transport W levB hEq hφ T hT c s ζ ⟨_, hζ⟩ (by rw [hQq]; exact cc_lev_q W c ζ ⟨_, hζ⟩ hp1)
      hp i1 i2

end W

end Formalism.MainNotions.UnusedSlot80.LevR

namespace Formalism.MainNotions.UnusedSlot80

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

def PtEx (D : D7) (HW : HWOf D.loc) : Prop :=
  Formalism.MainNotions.WachCoordinates.AtCaseA fun l _ K LL h =>
    ∀ (c : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (ζ : ↥LL.1), IsPrimitiveRoot ζ l →
      ∃ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW h.2.2 c ζ τ

theorem levCoeff_of_pt (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (h4 : Formalism.MainNotions.DeltaInvariantLattices.P4 D HW F Cm) (hpt : PtEx D HW) :
    LevCoeff D HW F := by
  intro l _ K LL hA h5
  have tie := ((Cm l).C K 1 LL hA.2.2).tie
  have hs := (HW l).W_s K 1 LL hA.2.2
  have hp : ((((D.loc l).PD K).p : ℕ) : ↥LL.1) ≠ 0 := by
    intro h
    have hv := ((HW l).W K 1 LL hA.2.2).v_l
    rw [h, AddValuation.map_zero] at hv
    exact WithTop.top_ne_one hv
  have hsurj : Function.Surjective (algebraMap ↥(K0 K) ↥K.1) :=
    fun x => ⟨⟨x, x.2, hA.1 x.2⟩, rfl⟩
  refine LevR.level_condition_of_level_zero _ ((Cm l).C K 1 LL hA.2.2).tie.levB hs
    ((Cm l).C K 1 LL hA.2.2).tie.levN_eq ((Cm l).C K 1 LL hA.2.2).tie.levB_φ hp ?_
  intro T hT c ζ hζ
  have hζl : IsPrimitiveRoot ζ l := by rwa [(D.loc l).PD_p] at hζ
  obtain ⟨τ, hτ⟩ := hpt l K LL hA h5 c ζ hζl
  have hover : ∀ x : ↥(K0 K), τ (algebraMap ↥(K0 K) ↥K.1 x) = ((HW l).W K 1 LL hA.2.2).emb c x := by
    obtain ⟨τs, ⟨hemb, -⟩, hres⟩ := hτ
    intro x
    have hy : (x : Om l) ∈ Ks K 1 := (le_sup_left : K0 K ≤ Ks K 1) x.2
    rw [hres (algebraMap ↥(K0 K) ↥K.1 x) ⟨x, hy⟩ rfl]
    exact hemb x ⟨x, hy⟩ rfl
  have h4' := ((h4 l K 1 LL hA.2.2 T hT).2 c ζ τ hτ).2
  exact LevR.lev0 _ T c ζ τ (LevR.ιDi_le _ T c τ hover hsurj) h4'

end Formalism.MainNotions.UnusedSlot80

namespace Formalism.MainNotions.UnusedSlot80.LevR

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

theorem root_eq_one {l : ℕ} [Fact l.Prime] (t : ℚ_[l]) (ht : t ^ (l - 1) = 1) (h1 : ‖t - 1‖ < 1) :
    t = 1 := by
  have hn : ‖t‖ ≤ 1 := by
    have e : t = (t - 1) + 1 := by ring
    rw [e]
    exact (Padic.nonarchimedean _ _).trans (max_le h1.le (by simp))
  obtain ⟨T, rfl⟩ : ∃ T : ℤ_[l], (T : ℚ_[l]) = t := ⟨⟨t, hn⟩, rfl⟩
  have hT1 : PadicInt.toZMod (T - 1) = 0 := by
    rw [← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits,
      PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_one]
    exact h1
  have hT : PadicInt.toZMod T = 1 := by
    rw [map_sub, map_one, sub_eq_zero] at hT1
    exact hT1
  have hS : PadicInt.toZMod (∑ i ∈ Finset.range (l - 1), T ^ i) ≠ 0 := by
    rw [map_sum]
    simp only [map_pow, hT, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hd
    have h2 := (Fact.out : l.Prime).two_le
    have := Nat.le_of_dvd (by omega) hd
    omega
  have hTl : T ^ (l - 1) = 1 := by
    apply Subtype.ext
    rw [PadicInt.coe_pow, PadicInt.coe_one]
    exact ht
  have hprod := geom_sum_mul T (l - 1)
  rw [hTl, sub_self] at hprod
  have hS0 : (∑ i ∈ Finset.range (l - 1), T ^ i) ≠ 0 := fun h => hS (by rw [h, map_zero])
  have h3 : T - 1 = 0 := (mul_eq_zero.mp hprod).resolve_left hS0
  rw [sub_eq_zero.mp h3, PadicInt.coe_one]

section Trans

variable (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)

theorem root_of_unity_primitive (l : ℕ) [Fact l.Prime] : IsPrimitiveRoot ((D.loc l).ζQ 1) l := by
  have h1 : (D.loc l).ζQ 1 ^ l = 1 := by
    rw [(D.loc l).ζQ_succ 0, (D.loc l).ζQ_zero]
  have ho := orderOf_eq_prime h1 (D.loc l).ζQ_one
  have := IsPrimitiveRoot.orderOf ((D.loc l).ζQ 1)
  rwa [ho] at this

theorem card_delF (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F) (l : ℕ) [Fact l.Prime] (K LL : FinExt l)
    (hA : CaseA K LL) : ((HW l).W K 1 LL hA.2.2).DelF.card = l - 1 := by
  have : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have hc := Formalism.MainNotions.LiftingTheory.gen_one_crys ((HW l).W K 1 LL hA.2.2)
  have hs : ((HW l).W K 1 LL hA.2.2).s = 1 := (HW l).W_s K 1 LL hA.2.2
  have hp : ((D.loc l).PD K).p ≠ 2 := by rw [(D.loc l).PD_p]; exact hA.2.1
  have h := ((h9 l K 1 LL hA.2.2 _ hc) hs hp).1
  rw [h, Formalism.MainNotions.UnusedSlot80.finrank_K0_eq_one_of_le_Kur hA.1, Nat.div_one, (D.loc l).PD_p]

end Trans

section TransW

set_option maxHeartbeats 800000 in

theorem trans_prim {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K LL : FinExt l}
    (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K)))
    (hcard : W.DelF.card = l - 1) (hζ₁ : IsPrimitiveRoot (P.ζQ 1) l)
    (ζ' : Om l) (hζ' : IsPrimitiveRoot ζ' l) :
    ∃ g : ↥(GK K), (g : GQ l) (P.ζQ 1) = ζ' := by
  classical
  have hl2 := (Fact.out : l.Prime).two_le

  obtain ⟨H, hH⟩ : ∃ H : Subgroup W.Gam, (H : Set W.Gam) = ↑W.DelF := ⟨
    { carrier := ↑W.DelF
      mul_mem' := by
        intro a b ha hb
        simp only [Finset.mem_coe, W.DelF_def] at ha hb ⊢
        obtain ⟨k, hk, hak⟩ := ha
        obtain ⟨k', hk', hbk⟩ := hb
        exact ⟨k * k', Nat.mul_pos hk hk', by
          rw [mul_pow, pow_mul, hak, one_pow, one_mul, mul_comm, pow_mul, hbk, one_pow]⟩
      one_mem' := by
        simp only [Finset.mem_coe, W.DelF_def]
        exact ⟨1, one_pos, one_pow _⟩
      inv_mem' := by
        intro a ha
        simp only [Finset.mem_coe, W.DelF_def] at ha ⊢
        obtain ⟨k, hk, hak⟩ := ha
        exact ⟨k, hk, by rw [inv_pow, hak, inv_one]⟩ }, rfl⟩
  have memH : ∀ x, x ∈ H ↔ x ∈ W.DelF := fun x => by
    rw [← SetLike.mem_coe, hH, Finset.mem_coe]
  have hHcard : Nat.card H = l - 1 := by
    rw [← hcard, ← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight memH)
  have hexp : ∀ δ ∈ W.DelF, δ ^ (l - 1) = 1 := by
    intro δ hδ
    have h : (⟨δ, (memH δ).mpr hδ⟩ : H) ^ (l - 1) = 1 := by
      rw [← hHcard]
      exact pow_card_eq_one'
    have h2 := congrArg (fun y : H => (y : W.Gam)) h
    simpa only [Subgroup.coe_pow, Subgroup.coe_one] using h2
  have hζpow : P.ζQ 1 ^ (l ^ 1) = 1 := by rw [pow_one]; exact hζ₁.pow_eq_one

  have key : ∀ g : ↥(GK K), (g : GQ l) (P.ζQ 1) = P.ζQ 1 → W.resΓ g ∈ W.DelF → W.resΓ g = 1 := by
    intro g hg hΔ
    obtain ⟨a, ha, hga⟩ := P.χQ_cyc (g : GQ l) 1 (P.ζQ 1) (by rw [pow_one]; exact hζ₁.pow_eq_one)
    rw [hg] at hga
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hga
      exact P.ζQ_one hga
    have hdvd : (l : ℤ) ∣ (a : ℤ) - 1 := by
      have e : P.ζQ 1 ^ (a - 1) = 1 := by
        have h0 : P.ζQ 1 ≠ 0 := hζ₁.ne_zero (by omega)
        apply mul_right_cancel₀ h0
        rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr ha0), ← hga, one_mul]
      have := (hζ₁.pow_eq_one_iff_dvd (a - 1)).mp e
      have h' : ((a - 1 : ℕ) : ℤ) = (a : ℤ) - 1 := by
        rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr ha0)]; simp
      rw [← h']
      exact_mod_cast this
    have hna : ‖((a : ℚ_[l]) - 1)‖ ≤ (l : ℝ) ^ (-((1 : ℕ) : ℤ)) := by
      have := (Padic.norm_int_le_pow_iff_dvd ((a : ℤ) - 1) 1).mpr (by simpa using hdvd)
      simpa using this
    have ht1 : ‖(P.χQ (g : GQ l) : ℚ_[l]) - 1‖ < 1 := by
      have e : (P.χQ (g : GQ l) : ℚ_[l]) - 1 = ((P.χQ (g : GQ l) : ℚ_[l]) - a) + ((a : ℚ_[l]) - 1) := by
        ring
      rw [e]
      refine lt_of_le_of_lt ((Padic.nonarchimedean _ _).trans (max_le ha hna)) ?_
      have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
      rw [zpow_neg, zpow_natCast, pow_one]
      exact inv_lt_one_of_one_lt₀ hl1

    have hres := W.χΓ_res g
    have hPD := P.PD_χ K g
    have htl : (P.χQ (g : GQ l) : ℚ_[l]) ^ (l - 1) = 1 := by
      have e1 : (W.χΓ (W.resΓ g)) ^ (l - 1) = 1 := by rw [← map_pow, hexp _ hΔ, map_one]
      have e2 : algebraMap ↥(OL LL) ↥LL.1 ((W.χΓ (W.resΓ g) : ↥(OL LL))) ^ (l - 1) = 1 := by
        rw [← map_pow, ← Units.val_pow_eq_pow_val, e1, Units.val_one, map_one]
      rw [hres, ← map_pow] at e2
      have e3 : ((((P.PD K).χ g : ℚ_[l]ˣ) : ℚ_[l])) ^ (l - 1) = 1 :=
        (algebraMap ℚ_[l] ↥LL.1).injective (by rw [e2, map_one])
      rwa [hPD] at e3
    have ht := root_eq_one _ htl ht1
    have e4 : algebraMap ↥(OL LL) ↥LL.1 ((W.χΓ (W.resΓ g) : ↥(OL LL))) = 1 := by
      rw [hres, hPD, ht, map_one]
    have e5 : (W.χΓ (W.resΓ g) : ↥(OL LL)) = 1 :=
      Subtype.val_injective (by simpa using e4)
    exact W.χΓ_inj (by rw [map_one]; exact Units.ext e5)

  have hlift : ∀ δ : ↥W.DelF, ∃ g : ↥(GK K), W.resΓ g = δ := fun δ => W.resΓ_onto δ
  choose gδ hgδ using hlift
  have hcyc : ∀ δ : ↥W.DelF, ∃ a : ℕ, ((gδ δ : ↥(GK K)) : GQ l) (P.ζQ 1) = P.ζQ 1 ^ a := fun δ => by
    obtain ⟨a, -, h⟩ := P.χQ_cyc ((gδ δ : ↥(GK K)) : GQ l) 1 (P.ζQ 1) (by rw [pow_one]; exact hζ₁.pow_eq_one)
    exact ⟨a, h⟩
  choose aδ haδ using hcyc
  have hne : ∀ δ, ((aδ δ : ℕ) : ZMod l) ≠ 0 := by
    intro δ h
    rw [ZMod.natCast_eq_zero_iff] at h
    have h1 : P.ζQ 1 ^ aδ δ = 1 := (hζ₁.pow_eq_one_iff_dvd _).mpr h
    rw [← haδ δ] at h1
    have h2 : ((gδ δ : ↥(GK K)) : GQ l) (P.ζQ 1) = ((gδ δ : ↥(GK K)) : GQ l) 1 := by rw [h1, map_one]
    exact P.ζQ_one (((gδ δ : ↥(GK K)) : GQ l).injective h2)
  let U : ↥W.DelF → (ZMod l)ˣ := fun δ => Units.mk0 _ (hne δ)
  have hpowmod : ∀ n : ℕ, P.ζQ 1 ^ n = P.ζQ 1 ^ (n % l) := fun n => by
    conv_lhs => rw [← Nat.mod_add_div n l, pow_add, pow_mul, hζ₁.pow_eq_one, one_pow, mul_one]
  have hUinj : Function.Injective U := by
    intro δ δ' h
    have h1 : ((aδ δ : ℕ) : ZMod l) = ((aδ δ' : ℕ) : ZMod l) := congrArg Units.val h
    rw [ZMod.natCast_eq_natCast_iff] at h1
    have h2 : ((gδ δ : ↥(GK K)) : GQ l) (P.ζQ 1) = ((gδ δ' : ↥(GK K)) : GQ l) (P.ζQ 1) := by
      rw [haδ, haδ, hpowmod (aδ δ), hpowmod (aδ δ'), h1]
    set g := (gδ δ')⁻¹ * gδ δ
    have hg : (g : GQ l) (P.ζQ 1) = P.ζQ 1 := by
      simp only [g, Subgroup.coe_mul, Subgroup.coe_inv, AlgEquiv.mul_apply, h2]
      exact AlgEquiv.symm_apply_apply _ _
    have hgΔ : W.resΓ g = (δ' : W.Gam)⁻¹ * δ := by simp [g, hgδ]
    have hmem : W.resΓ g ∈ W.DelF := by
      rw [hgΔ]
      exact (memH _).mp (H.mul_mem (H.inv_mem ((memH _).mpr δ'.2)) ((memH _).mpr δ.2))
    have := key g hg hmem
    rw [hgΔ, inv_mul_eq_one] at this
    exact Subtype.ext this.symm
  have hUbij : Function.Bijective U := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hUinj, by rw [Fintype.card_coe, hcard, ZMod.card_units]⟩
  obtain ⟨i, hi, hζi⟩ := hζ₁.eq_pow_of_pow_eq_one hζ'.pow_eq_one
  have hi0 : ((i : ℕ) : ZMod l) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hd
    have : i = 0 := Nat.eq_zero_of_dvd_of_lt hd hi
    subst this
    rw [pow_zero] at hζi
    exact hζ'.ne_one (Fact.out : l.Prime).one_lt hζi.symm
  obtain ⟨δ, hδ⟩ := hUbij.2 (Units.mk0 _ hi0)
  have h1 : ((aδ δ : ℕ) : ZMod l) = ((i : ℕ) : ZMod l) := congrArg Units.val hδ
  rw [ZMod.natCast_eq_natCast_iff] at h1
  refine ⟨gδ δ, ?_⟩
  rw [haδ, hpowmod, h1, ← hpowmod, hζi]

end TransW

end Formalism.MainNotions.UnusedSlot80.LevR

namespace Formalism.MainNotions.UnusedSlot80

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

theorem points_exist_of_ring_condition (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F) : PtEx D HW := by
  intro l _ K LL hA h5 c ζ hζ
  have : Algebra.IsAlgebraic ↥(K0 K) (Om l) := Algebra.IsAlgebraic.tower_top (K := ℚ_[l]) _
  obtain ⟨σ, hσ⟩ := IsAlgClosed.surjective_domRestrict_of_isAlgebraic (K := ℚ_[l]) (L := ↥(K0 K))
    (M := Om l) (E := Om l) ((LL.1.val).comp (((HW l).W K 1 LL hA.2.2).emb c))
  have hσx : ∀ x : ↥(K0 K),
      σ (x : Om l) = ((((HW l).W K 1 LL hA.2.2).emb c x : ↥LL.1) : Om l) := fun x => by
    have := congrArg (fun f => f x) hσ
    simpa [AlgHom.domRestrict] using this
  have hζ₁ := LevR.root_of_unity_primitive D l
  have hσinj : Function.Injective σ := σ.toRingHom.injective
  have hζO : IsPrimitiveRoot ((ζ : ↥LL.1) : Om l) l :=
    hζ.map_of_injective (f := LL.1.val) Subtype.val_injective
  have hσζ₁ : IsPrimitiveRoot (σ ((D.loc l).ζQ 1)) l := hζ₁.map_of_injective hσinj
  have : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  obtain ⟨b, -, hb⟩ := hσζ₁.eq_pow_of_pow_eq_one hζO.pow_eq_one
  have hβ : IsPrimitiveRoot ((D.loc l).ζQ 1 ^ b) l := by
    apply IsPrimitiveRoot.of_map_of_injective (f := σ) _ hσinj
    rw [map_pow, hb]
    exact hζO
  obtain ⟨g, hg⟩ := LevR.trans_prim (D.loc l) ((HW l).W K 1 LL hA.2.2)
    (LevR.card_delF D HW F h9 l K LL hA) hζ₁ _ hβ
  have hmem : ∀ y, ((σ.comp (g : GQ l).toAlgHom).comp (Ks K 1).val) y ∈ LL.1 :=
    hA.2.2.2.2.2 _
  let τs : ↥(Ks K 1) →ₐ[ℚ_[l]] ↥LL.1 :=
    ((σ.comp (g : GQ l).toAlgHom).comp (Ks K 1).val).codRestrict LL.1.toSubalgebra hmem
  refine ⟨τs.comp (IntermediateField.inclusion hA.2.2.2.2.1), τs,
    ⟨fun x y hxy => ?_, fun y hy => ?_⟩, fun x y hxy => ?_⟩
  · apply Subtype.ext
    show σ ((g : GQ l) (y : Om l)) = _
    have hgx : (g : GQ l) (x : Om l) = x :=
      (IntermediateField.mem_fixingSubgroup_iff K.1 (g : GQ l)).mp g.2 _
        ((inf_le_left : K0 K ≤ K.1) x.2)
    rw [hxy, hgx, hσx]
  · apply Subtype.ext
    show σ ((g : GQ l) (y : Om l)) = _
    rw [hy, hg, map_pow, hb]
  · show τs _ = τs y
    congr 1
    exact Subtype.ext hxy.symm

theorem levCoeff_of (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (h : AdmTools D HW F Cm) : LevCoeff D HW F :=
  levCoeff_of_pt D HW F Cm h.2.1 (points_exist_of_ring_condition D HW F h.2.2)

theorem tools_unramified_statement (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) : FiltrationPropertiesTheorem D HW F Cm := fun h =>
  tools_unramified_of_level_coeff D HW F Cm (levCoeff_of D HW F Cm h) h

end Formalism.MainNotions.UnusedSlot80
