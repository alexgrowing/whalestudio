import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsIndepSections

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw

noncomputable section

namespace GlobalTheory.SecGrowth

section Poly

variable {σ R A : Type} [CommRing R] [CommRing A]

theorem eval₂Hom_mul_of_isHomogeneous (c : R →+* A) (u : A) (x : σ → A) {F : MvPolynomial σ R} {t : ℕ}
    (hF : F.IsHomogeneous t) :
    MvPolynomial.eval₂Hom c (fun j => u * x j) F = u ^ t * MvPolynomial.eval₂Hom c x F := by
  simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [hF.degree_eq_sum_deg_support hd]
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  ring

theorem exists_isHomogeneous_eval₂Hom_eq (c : R →+* A) (x : σ → A) (i : σ) (hi : x i = 1)
    (p : MvPolynomial σ R) {t : ℕ} (hp : p.totalDegree ≤ t) :
    ∃ F : MvPolynomial σ R, F.IsHomogeneous t ∧
      MvPolynomial.eval₂Hom c x F = MvPolynomial.eval₂Hom c x p := by
  refine ⟨∑ d ∈ Finset.range (p.totalDegree + 1),
    MvPolynomial.homogeneousComponent d p * MvPolynomial.X i ^ (t - d), ?_, ?_⟩
  · refine MvPolynomial.IsHomogeneous.sum _ _ _ fun d hd => ?_
    have h := (MvPolynomial.homogeneousComponent_isHomogeneous d p).mul
      (MvPolynomial.isHomogeneous_X_pow (R := R) i (t - d))
    have hd' := Finset.mem_range.1 hd
    rwa [show d + (t - d) = t by omega] at h
  · conv_rhs => rw [← MvPolynomial.sum_homogeneousComponent p]
    simp only [map_sum, map_mul, map_pow, MvPolynomial.eval₂Hom_X', hi, one_pow, _root_.mul_one]

end Poly

section Sections

variable {X : Scheme.{0}}

theorem rs_eval₂Hom {R σ : Type} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R)) {U V : X.Opens} (h : V ≤ U)
    (x : σ → Γ(X, U)) (F : MvPolynomial σ R) :
    rs X h (MvPolynomial.eval₂Hom (cst f U) x F) = MvPolynomial.eval₂Hom (cst f V) (fun j => rs X h (x j)) F := by
  rw [MvPolynomial.map_eval₂Hom]
  congr 2
  exact RingHom.ext fun r => rs_cst f h r

def polySec {R σ : Type} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R)) {H : LB X} (s : σ → LB.Sec H)
    {t : ℕ} {F : MvPolynomial σ R} (hF : F.IsHomogeneous t) : LB.Sec (pw H t) where
  f := fun k => MvPolynomial.eval₂Hom (cst f (H.U k)) (fun j => (s j).f k) F
  compat := fun k l => by
    have h₁ := rs_eval₂Hom f (inf_le_left : H.U k ⊓ H.U l ≤ H.U k) (fun j => (s j).f k) F
    have h₂ := rs_eval₂Hom f (inf_le_right : H.U k ⊓ H.U l ≤ H.U l) (fun j => (s j).f l) F
    have h₃ : (fun j => rs X (inf_le_left : H.U k ⊓ H.U l ≤ H.U k) ((s j).f k)) =
        fun j => (H.g k l).val * rs X (inf_le_right : H.U k ⊓ H.U l ≤ H.U l) ((s j).f l) :=
      funext fun j => (s j).compat k l
    rw [h₃, eval₂Hom_mul_of_isHomogeneous _ _ _ hF, ← h₂] at h₁
    refine h₁.trans (congrArg₂ (· * ·) ?_ rfl)
    change _ = ((H.g k l) ^ (t : ℤ)).val
    rw [zpow_natCast, Units.val_pow_eq_pow_val]

theorem sec_eq_zero [IsIntegral X] {M : LB X} (σ : LB.Sec M) {k₀ : M.ι} {W : X.Opens} (hW : W ≤ M.U k₀)
    [Nonempty W] (h : rs X hW (σ.f k₀) = 0) (k : M.ι) : σ.f k = 0 := by
  have h₀ : σ.f k₀ = 0 := map_injective_of_isIntegral X (homOfLE hW) (h.trans (map_zero _).symm)
  by_cases hk : M.U k = ⊥
  · have : Subsingleton Γ(X, M.U k) := by
      rw [hk]; infer_instance
    exact Subsingleton.elim _ _
  · have hne : Nonempty (M.U k ⊓ M.U k₀ : X.Opens) := by
      obtain ⟨x, hx⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 hk
      obtain ⟨y⟩ := ‹Nonempty W›
      obtain ⟨z, hz⟩ := nonempty_preirreducible_inter (M.U k).isOpen (M.U k₀).isOpen ⟨x, hx⟩ ⟨y.1, hW y.2⟩
      exact ⟨⟨z, hz⟩⟩
    apply map_injective_of_isIntegral X (homOfLE (inf_le_left : M.U k ⊓ M.U k₀ ≤ M.U k))
    refine (σ.compat k k₀).trans ?_
    rw [h₀, map_zero, map_zero, mul_zero]

def transSec {M M' : LB X} (a : M'.ι → M.ι) (ha : ∀ j, M'.U j ≤ M.U (a j))
    (hg : ∀ j j', M'.g j j' = res (inf_le_inf (ha j) (ha j')) (M.g (a j) (a j'))) (σ : LB.Sec M) : LB.Sec M' where
  f := fun j => rs X (ha j) (σ.f (a j))
  compat := fun j j' => by
    have h := congrArg (rs X (inf_le_inf (ha j) (ha j'))) (σ.compat (a j) (a j'))
    rw [map_mul] at h
    rw [hg]
    exact (rs_rs _ _ _).trans (((rs_rs _ _ _).symm.trans h).trans
      (congrArg₂ (· * ·) rfl ((rs_rs _ _ _).trans (rs_rs _ _ _).symm)))

end Sections

section Growth

theorem growth_of_veryAmpleBy {K : Type} [Field K] {X : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of K)) {H : LB X} {m : ℕ} (s : Fin (m + 1) → LB.Sec H) (hs : VeryAmpleBy f H s)
    (g t₀ : ℕ)
    (hgen : ∀ t : ℕ, t₀ ≤ t → ∀ σ : LB.Sec (pw H t), ∃ F : MvPolynomial (Fin (m + 1)) K, F.IsHomogeneous t ∧
      ∀ k : H.ι, σ.f k = MvPolynomial.eval₂Hom (cst f (H.U k)) (fun j => (s j).f k) F)
    (hGK : ∀ (B : Type) [CommRing B] [IsDomain B] [Algebra K B] (r : Fin (m + 1) → B),
      Function.Surjective (MvPolynomial.aeval r : MvPolynomial (Fin (m + 1)) K →ₐ[K] B) → Algebra.trdeg K B = g →
      ∃ c C : ℕ, 1 ≤ c ∧ ∀ t : ℕ, 1 ≤ t →
        t ^ g ≤ c * Module.finrank K ((MvPolynomial.restrictTotalDegree (Fin (m + 1)) K t).map
          (MvPolynomial.aeval r : MvPolynomial (Fin (m + 1)) K →ₐ[K] B).toLinearMap) ∧
        Module.finrank K ((MvPolynomial.restrictTotalDegree (Fin (m + 1)) K t).map
          (MvPolynomial.aeval r : MvPolynomial (Fin (m + 1)) K →ₐ[K] B).toLinearMap) ≤ C * t ^ g)
    (htr : ∀ (B : Type) [CommRing B] [Nontrivial B] [Algebra K B] (j : Spec (CommRingCat.of B) ⟶ X),
      IsOpenImmersion j → j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K B)) → Algebra.trdeg K B = g)
    (V : ℕ → Type) [∀ t, AddCommGroup (V t)] [∀ t, Module K (V t)] [∀ t, Module.Finite K (V t)]
    (ev : ∀ t : ℕ, V t → LB.Sec (pw H t))
    (hadd : ∀ t a b (k : H.ι), (ev t (a + b)).f k = (ev t a).f k + (ev t b).f k)
    (hsmul : ∀ t (c : K) a (k : H.ι), (ev t (c • a)).f k = cst f (H.U k) c * (show Γ(X, H.U k) from (ev t a).f k))
    (hinj : ∀ t a, (∀ k : H.ι, (ev t a).f k = 0) → a = 0)
    (hsurj : ∀ (t : ℕ) (σ : LB.Sec (pw H t)), ∃ a, ∀ k : H.ι, (ev t a).f k = σ.f k) :
    ∃ c C : ℕ, 1 ≤ c ∧ ∀ t : ℕ, 1 ≤ t →
      t ^ g ≤ c * Module.finrank K (V t) ∧ Module.finrank K (V t) ≤ C * t ^ g := by
  obtain ⟨x⟩ : Nonempty X := inferInstance
  have hx : x ∈ ⨆ i, nonzeroLocus (s i) := by rw [hs.1]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  obtain ⟨k₀, hk₀⟩ := TopologicalSpace.Opens.mem_iSup.1 hi
  obtain ⟨hD, r, hr, hrs⟩ := hs.2 i
  let W : X.Opens := X.basicOpen ((s i).f k₀)
  have hWD : W ≤ nonzeroLocus (s i) := le_iSup (fun k => X.basicOpen ((s i).f k)) k₀
  have hWU : W ≤ H.U k₀ := X.basicOpen_le _
  haveI : Nonempty W := ⟨⟨x, hk₀⟩⟩
  haveI : Nonempty (nonzeroLocus (s i)) := ⟨⟨x, hi⟩⟩
  obtain ⟨u, hu⟩ : IsUnit (rs X hWU ((s i).f k₀)) := X.toRingedSpace.isUnit_res_basicOpen _
  letI : Algebra K Γ(X, nonzeroLocus (s i)) := (cst f _).toAlgebra
  letI : Algebra K Γ(X, W) := (cst f _).toAlgebra
  let ρ : Γ(X, nonzeroLocus (s i)) →ₐ[K] Γ(X, W) :=
    { rs X hWD with commutes' := fun c => rs_cst f hWD c }
  have hρ : Function.Injective ρ := map_injective_of_isIntegral X (homOfLE hWD)
  have hsr : ∀ j, rs X hWU ((s j).f k₀) = u.val * rs X hWD (r j) := fun j => by
    have h := congrArg (rs X (le_inf hWD hWU)) (hr j k₀)
    rw [map_mul, rs_rs, rs_rs, rs_rs, ← hu] at h
    exact h.trans (mul_comm _ _)
  have hri : r i = 1 := by
    apply hρ
    have h := hsr i
    rw [← hu] at h
    rw [map_one]
    exact (Units.mul_right_inj u).1 (h.symm.trans (_root_.mul_one _).symm)
  have key : ∀ (t : ℕ) (F : MvPolynomial (Fin (m + 1)) K), F.IsHomogeneous t →
      rs X hWU (MvPolynomial.eval₂Hom (cst f (H.U k₀)) (fun j => (s j).f k₀) F) * (u⁻¹).val ^ t =
        ρ (MvPolynomial.aeval r F) := fun t F hF => by
    rw [rs_eval₂Hom, funext hsr, eval₂Hom_mul_of_isHomogeneous _ _ _ hF, ← rs_eval₂Hom, mul_right_comm,
      ← mul_pow, Units.mul_inv, one_pow, _root_.one_mul]
    rfl
  let Φ : ∀ t : ℕ, V t →ₗ[K] Γ(X, W) := fun t =>
    { toFun := fun a => rs X hWU ((ev t a).f k₀) * (u⁻¹).val ^ t
      map_add' := fun a b => by
        rw [hadd]
        exact (congrArg (· * _) (map_add (rs X hWU) _ _)).trans (add_mul _ _ _)
      map_smul' := fun c a => by
        rw [hsmul, map_mul, rs_cst, _root_.mul_assoc]
        rfl }
  have hΦ : ∀ t, Function.Injective (Φ t) := fun t => by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    have h : rs X hWU ((ev t a).f k₀) = 0 := ((u⁻¹.isUnit.pow t).mul_left_eq_zero).1 ha
    exact hinj t a (sec_eq_zero (M := pw H t) (ev t a) (k₀ := k₀) hWU h)
  let P : ℕ → Submodule K Γ(X, nonzeroLocus (s i)) := fun t =>
    (MvPolynomial.restrictTotalDegree (Fin (m + 1)) K t).map
      (MvPolynomial.aeval r : MvPolynomial (Fin (m + 1)) K →ₐ[K] Γ(X, nonzeroLocus (s i))).toLinearMap
  have hP : ∀ t, Module.finrank K ((P t).map ρ.toLinearMap) = Module.finrank K (P t) := fun t =>
    (Submodule.equivMapOfInjective ρ.toLinearMap hρ (P t)).finrank_eq.symm
  have hV : ∀ t, Module.finrank K (LinearMap.range (Φ t)) = Module.finrank K (V t) := fun t =>
    LinearMap.finrank_range_of_inj (hΦ t)
  have hle : ∀ t, (P t).map ρ.toLinearMap ≤ LinearMap.range (Φ t) := by
    rintro t _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    obtain ⟨F, hF, hFp⟩ := exists_isHomogeneous_eval₂Hom_eq (cst f _) r i hri p
      ((MvPolynomial.mem_restrictTotalDegree _ _ _).1 hp)
    obtain ⟨a, ha⟩ := hsurj t (polySec f s hF)
    refine ⟨a, ?_⟩
    change rs X hWU ((ev t a).f k₀) * (u⁻¹).val ^ t = _
    rw [ha]
    exact (key t F hF).trans (congrArg ρ hFp)
  have hge : ∀ t, t₀ ≤ t → LinearMap.range (Φ t) ≤ (P t).map ρ.toLinearMap := by
    rintro t ht _ ⟨a, rfl⟩
    obtain ⟨F, hF, hFa⟩ := hgen t ht (ev t a)
    refine ⟨_, ⟨F, (MvPolynomial.mem_restrictTotalDegree _ _ _).2 hF.totalDegree_le, rfl⟩, ?_⟩
    change _ = rs X hWU ((ev t a).f k₀) * (u⁻¹).val ^ t
    rw [hFa]
    exact (key t F hF).symm
  have htd : Algebra.trdeg K Γ(X, nonzeroLocus (s i)) = g := by
    refine htr Γ(X, nonzeroLocus (s i)) hD.fromSpec inferInstance ?_
    have h := IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top _) hD le_top
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp] at h
    exact h.symm
  obtain ⟨c, C, hc, hcC⟩ := hGK Γ(X, nonzeroLocus (s i)) r hrs htd
  refine ⟨c, C + ∑ t ∈ Finset.range t₀, Module.finrank K (V t), hc, fun t ht => ⟨?_, ?_⟩⟩
  · refine (hcC t ht).1.trans (Nat.mul_le_mul_left _ ?_)
    exact (hP t).symm.trans_le ((Submodule.finrank_mono (hle t)).trans (hV t).le)
  · by_cases h : t₀ ≤ t
    · refine le_trans ?_ ((hcC t ht).2.trans (Nat.mul_le_mul_right _ (Nat.le_add_right _ _)))
      rw [← hV, le_antisymm (hge t h) (hle t)]
      exact (hP t).le
    · have h₁ : Module.finrank K (V t) ≤ ∑ t ∈ Finset.range t₀, Module.finrank K (V t) :=
        Finset.single_le_sum (f := fun t => Module.finrank K (V t)) (fun _ _ => Nat.zero_le _)
          (Finset.mem_range.2 (not_le.1 h))
      exact h₁.trans ((Nat.le_add_left _ C).trans (Nat.le_mul_of_pos_right _ (Nat.pow_pos ht)))

end Growth

section Modules

theorem finite_of_not_linearIndependent {R V : Type} [CommRing R] (hR : IsField R) [AddCommGroup V] [Module R V]
    (n : ℕ) (h : ∀ b : Fin n → V, ¬ LinearIndependent R b) : Module.Finite R V := by
  letI := hR.toField
  haveI : Module.Free R V := Module.Free.of_divisionRing R V
  by_contra hV
  obtain ⟨b, hb⟩ := exists_linearIndependent_of_le_rank (R := R) (M := V) (n := n)
    ((Cardinal.natCast_lt_aleph0 (n := n)).le.trans (not_lt.1 fun hlt => hV (Module.rank_lt_aleph0_iff.1 hlt)))
  exact h b hb

theorem finrank_compHom {K R V : Type} [CommRing K] [CommRing R] (e : K ≃+* R) [AddCommGroup V] [Module R V] :
    letI := Module.compHom V e.toRingHom
    Module.finrank K V = Module.finrank R V := by
  letI := Module.compHom V e.toRingHom
  exact congrArg Cardinal.toNat (rank_eq_of_equiv_equiv e (AddEquiv.refl V) e.bijective fun _ _ => rfl)

theorem finite_compHom {K R V : Type} [CommRing K] [CommRing R] (e : K ≃+* R) [AddCommGroup V] [Module R V]
    [Module.Finite R V] :
    letI := Module.compHom V e.toRingHom
    Module.Finite K V := by
  letI := Module.compHom V e.toRingHom
  haveI : RingHomSurjective (e.symm : R →+* K) := ⟨e.symm.surjective⟩
  let φ : V →ₛₗ[(e.symm : R →+* K)] V :=
    { toFun := id
      map_add' := fun _ _ => rfl
      map_smul' := fun c v => congrArg (· • v) (e.apply_symm_apply c).symm }
  exact Module.Finite.of_surjective φ Function.surjective_id

end Modules

section Abelian

theorem finite_secM {K : Type} [Field K] (P : PolAV (Spec (CommRingCat.of K)))
    (hfin : ∀ M : LB P.A.left, M.IsLB → ∃ n : ℕ, ∀ s : Fin n → LB.Sec M,
      ∃ c : Fin n → Γ(Spec (CommRingCat.of K), ⊤), c ≠ 0 ∧
        ∀ i, ∑ k, (P.A.hom.appLE ⊤ (M.U i) le_top).hom (c k) * (s k).f i = 0) (a : ℤ) :
    Module.Finite Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤)
      (SecM P.A P.L a (baseOver (Spec (CommRingCat.of K)))) := by
  let T : Over (Spec (CommRingCat.of K)) := baseOver (Spec (CommRingCat.of K))
  obtain ⟨n, hn⟩ := hfin (LB.LinComb P.L (K := PUnit) (fun _ => 𝟙 P.A.left) (fun _ => a))
    (LB.isLB_linComb P.isLB _ _)
  refine finite_of_not_linearIndependent (isField_of_isIntegral_of_subsingleton (Spec (CommRingCat.of K))) n
    fun b hb => ?_
  let ρ : P.A ⟶ T ⊗ P.A := lift (Over.homMk P.A.hom (Category.comp_id _)) (𝟙 _)
  have ρ₂ : ρ.left ≫ (snd T P.A).left = 𝟙 _ := congrArg (fun q => q.left) (lift_snd _ _ : ρ ≫ _ = _)
  have ρ₁ : ρ.left ≫ (fst T P.A).left = P.A.hom := congrArg (fun q => q.left) (lift_fst _ _ : ρ ≫ _ = _)
  have ρ₃ : (snd T P.A).left ≫ ρ.left = 𝟙 _ := by
    apply pullback.hom_ext
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ρ₁).trans (pullback.condition.symm.trans
        ((Category.comp_id _).trans (Category.id_comp _).symm)))
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ρ₂).trans
        ((Category.comp_id _).trans (Category.id_comp _).symm))
  haveI : IsIso ρ.left := ⟨_, ρ₂, ρ₃⟩
  obtain ⟨c, hc, ha⟩ := hn fun i => PowSec.down P.L (snd T P.A).left ρ.left ρ₂ a (SecM.toSec P.A (b i))
  have h0 : ∑ i, (show Γ(T.left, ⊤) from c i) • b i = 0 := by
    refine Subtype.ext (funext fun j => ?_)
    obtain ⟨k, rfl⟩ : ∃ k, j = fun _ => k := ⟨j 0, funext fun q => by rw [Subsingleton.elim q 0]⟩
    refine PowSec.appLE_injective ρ.left _ _ (PowSec.chart_eq P.L (snd T P.A).left ρ.left ρ₂ (fun _ => k)) ?_
    refine Eq.trans ?_ ((ha (fun _ => k)).trans (map_zero _).symm)
    rw [Submodule.coe_sum]
    refine (congrArg _ (Finset.sum_apply _ _ _)).trans ?_
    refine (map_sum (ρ.left.appLE _ _ (PowSec.chart_eq P.L (snd T P.A).left ρ.left ρ₂ (fun _ => k)).le).hom
      _ _).trans (Finset.sum_congr rfl fun i _ => ?_)
    refine (map_mul _ (liftHom P.A _ (c i)) ((b i).1 fun _ => k)).trans (congrArg₂ (· * ·) ?_ rfl)
    have h1 := (Scheme.Hom.appLE_comp_appLE ρ.left (fst T P.A).left ⊤ _ _ (fun _ _ => trivial)
      (PowSec.chart_eq P.L (snd T P.A).left ρ.left ρ₂ (fun _ => k)).le).trans
      (PowSec.appLE_congr ρ₁ ⊤ _ _ (fun _ _ => trivial))
    exact congrArg (fun φ => φ.hom (c i)) h1
  exact hc (funext fun i => Fintype.linearIndependent_iff.1 hb _ h0 i)

variable {X Y : Scheme.{0}} (L : LB X) (π : Y ⟶ X)

theorem wchart_le_one (j : PUnit → L.ι) :
    LB.wchart L (fun _ : PUnit => π) j ≤ LB.wchart L (fun _ : Fin 1 => π) (fun _ => j PUnit.unit) :=
  fun _ hy => Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy PUnit.unit

theorem wchart_le_unit (j : Fin 1 → L.ι) :
    LB.wchart L (fun _ : Fin 1 => π) j ≤ LB.wchart L (fun _ : PUnit => π) (fun _ => j 0) :=
  fun _ hy => Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy 0

theorem lcg_pow_pow (N t : ℕ) (j j' : PUnit → L.ι) :
    (LB.lcg L (K := PUnit) (fun _ => π) (fun _ => 1) j j' ^ (N : ℤ)) ^ (t : ℤ) =
      res (inf_le_inf (wchart_le_one L π j) (wchart_le_one L π j'))
        (LB.lcg L (K := Fin 1) (fun _ => π) (fun _ => ((N * t : ℕ) : ℤ)) _ _) := by
  rw [LB.res_lcg, LB.lcg_pull, Fintype.prod_unique, ← zpow_mul, Nat.cast_mul]

theorem lcg_mul (N t : ℕ) (j j' : Fin 1 → L.ι) :
    LB.lcg L (K := Fin 1) (fun _ => π) (fun _ => ((N * t : ℕ) : ℤ)) j j' =
      res (inf_le_inf (wchart_le_unit L π j) (wchart_le_unit L π j'))
        ((LB.lcg L (K := PUnit) (fun _ => π) (fun _ => 1) _ _ ^ (N : ℤ)) ^ (t : ℤ)) := by
  rw [map_zpow, map_zpow, LB.lcg_pull, LB.res_res, LB.lcg, Fintype.prod_unique, ← zpow_mul, Nat.cast_mul]
  rfl

def toPw (N t : ℕ) (σ : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => π) (fun _ => ((N * t : ℕ) : ℤ)))) :
    LB.Sec (pw (pw (L.pull π) N) t) :=
  transSec (M := LB.LinComb L (K := Fin 1) (fun _ => π) (fun _ => ((N * t : ℕ) : ℤ)))
    (M' := pw (pw (L.pull π) N) t) (fun j _ => j PUnit.unit) (wchart_le_one L π) (lcg_pow_pow L π N t) σ

def ofPw (N t : ℕ) (σ : LB.Sec (pw (pw (L.pull π) N) t)) :
    LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => π) (fun _ => ((N * t : ℕ) : ℤ))) :=
  transSec (M := pw (pw (L.pull π) N) t)
    (M' := LB.LinComb L (K := Fin 1) (fun _ => π) (fun _ => ((N * t : ℕ) : ℤ)))
    (fun j _ => j 0) (wchart_le_unit L π) (lcg_mul L π N t) σ

end Abelian

theorem secM_finite_and_growth :
    (∀ (X S : Scheme.{0}) (f : X ⟶ S), Smooth f → GeometricallyConnected f → GeometricallyIntegral f) → (∀ (S : Scheme.{0}) (P : PolAV S) (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ S) (X : Scheme.{0}) (π : X ⟶ P.A.left) (f : X ⟶ Spec (CommRingCat.of R)), IsPullback π f P.A.hom t → ∃ N : ℕ, 1 ≤ N ∧ ∃ (m : ℕ) (s : Fin (m + 1) → LB.Sec (pw (P.L.pull π) N)), (pw (P.L.pull π) N).IsLB ∧ VeryAmpleBy f (pw (P.L.pull π) N) s) → (∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (M : LB P.A.left), M.IsLB → ∃ n : ℕ, ∀ s : Fin n → LB.Sec M, ∃ c : Fin n → Γ(Spec (CommRingCat.of K), ⊤), c ≠ 0 ∧ ∀ i, ∑ k, (P.A.hom.appLE ⊤ (M.U i) le_top).hom (c k) * (s k).f i = 0) → (∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) [IsNoetherianRing R] (H : LB X) (m : ℕ) (s : Fin (m + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t → ∀ σ : LB.Sec (pw H t), ∃ F : MvPolynomial (Fin (m + 1)) R, F.IsHomogeneous t ∧ ∀ k : H.ι, σ.f k = MvPolynomial.eval₂Hom (cst f (H.U k)) (fun j => (s j).f k) F) → (∀ (K B : Type) [Field K] [CommRing B] [IsDomain B] [Algebra K B] (m g : ℕ) (r : Fin m → B), Function.Surjective (MvPolynomial.aeval r : MvPolynomial (Fin m) K →ₐ[K] B) → Algebra.trdeg K B = g → ∃ c C : ℕ, 1 ≤ c ∧ ∀ t : ℕ, 1 ≤ t → t ^ g ≤ c * Module.finrank K ((MvPolynomial.restrictTotalDegree (Fin m) K t).map (MvPolynomial.aeval r : MvPolynomial (Fin m) K →ₐ[K] B).toLinearMap) ∧ Module.finrank K ((MvPolynomial.restrictTotalDegree (Fin m) K t).map (MvPolynomial.aeval r : MvPolynomial (Fin m) K →ₐ[K] B).toLinearMap) ≤ C * t ^ g) → (∀ (K : Type) [Field K] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of K)) (g : ℕ), SmoothOfRelativeDimension g f → ∀ (B : Type) [CommRing B] [Nontrivial B] [Algebra K B] (j : Spec (CommRingCat.of B) ⟶ X), IsOpenImmersion j → j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K B)) → Algebra.trdeg K B = g) → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))), (∀ j : ℕ, Module.Finite Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤) (SecM P.A P.L (j : ℤ) (baseOver (Spec (CommRingCat.of K))))) ∧ ∃ N c C : ℕ, 1 ≤ N ∧ 1 ≤ c ∧ ∀ t : ℕ, 1 ≤ t → t ^ P.g ≤ c * Module.finrank Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤) (SecM P.A P.L ((N * t : ℕ) : ℤ) (baseOver (Spec (CommRingCat.of K)))) ∧ Module.finrank Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤) (SecM P.A P.L ((N * t : ℕ) : ℤ) (baseOver (Spec (CommRingCat.of K)))) ≤ C * t ^ P.g := by
  intro hGI hProj hFin hGen hGK hTr K _ _ P
  have hfin := finite_secM P (hFin K P)
  refine ⟨fun j => hfin j, ?_⟩
  let T : Over (Spec (CommRingCat.of K)) := baseOver (Spec (CommRingCat.of K))
  let π : (T ⊗ P.A).left ⟶ P.A.left := (snd T P.A).left
  let f : (T ⊗ P.A).left ⟶ Spec (CommRingCat.of K) := (fst T P.A).left
  have hpb : IsPullback π f P.A.hom (𝟙 _) := (IsPullback.of_hasPullback T.hom P.A.hom).flip
  obtain ⟨N, hN, m, s, hH, hs⟩ := hProj _ P K (𝟙 _) _ π f hpb
  obtain ⟨t₀, ht₀⟩ := hGen K _ f _ m s hH hs
  have hgi := hGI _ _ P.A.hom P.isAb.smooth P.isAb.geomConnected
  haveI : IsIntegral (T ⊗ P.A).left := GeometricallyIntegral.geometrically_isIntegral _ _ _ hpb
  have hsm : SmoothOfRelativeDimension P.g f :=
    (smoothOfRelativeDimension_isStableUnderBaseChange P.g).of_isPullback hpb P.smoothDim
  let e : K ≃+* Γ(T.left, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm
  let V : ℕ → Type := fun t => SecM P.A P.L ((N * t : ℕ) : ℤ) T
  letI : ∀ t, Module K (V t) := fun t => Module.compHom (V t) e.toRingHom
  haveI : ∀ t, Module.Finite K (V t) := fun t => finite_compHom e
  have hrk : ∀ t, Module.finrank K (V t) = Module.finrank Γ(T.left, ⊤) (V t) := fun t => finrank_compHom e
  obtain ⟨c, C, hc, hcC⟩ := growth_of_veryAmpleBy f s hs P.g t₀ ht₀ (fun B _ _ _ r => hGK K B _ _ r)
    (hTr K _ f P.g hsm) V (fun t v => toPw P.L π N t (SecM.toSec P.A v))
    (fun t a b k => map_add (rs _ (wchart_le_one P.L π k)) _ _)
    (fun t c a k => (map_mul (rs _ (wchart_le_one P.L π k)) (cst f _ c) _).trans
      (congrArg₂ (· * ·) (rs_cst f _ c) rfl))
    (fun t a ha => by
      refine Subtype.ext (funext fun j => ?_)
      obtain ⟨k, rfl⟩ : ∃ k, j = fun _ => k := ⟨j 0, funext fun q => by rw [Subsingleton.elim q 0]⟩
      have h := congrArg (rs _ (wchart_le_unit P.L π (fun _ => k))) (ha fun _ => k)
      exact ((rs_rs _ _ _).trans (rs_self _ _)).symm.trans (h.trans (map_zero _)))
    (fun t σ => ⟨SecM.ofSec P.A (ofPw P.L π N t σ), fun k => (rs_rs _ _ _).trans (rs_self _ _)⟩)
  refine ⟨N, c, C, hN, hc, fun t ht => ?_⟩
  have h := hcC t ht
  rw [hrk] at h
  exact h

end GlobalTheory.SecGrowth
