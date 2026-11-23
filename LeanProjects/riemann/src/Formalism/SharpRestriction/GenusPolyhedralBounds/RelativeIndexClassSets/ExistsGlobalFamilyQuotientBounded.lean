import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.WeightedPrimeSumBound

noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

section LinAlgQ

theorem exists_den {R K V : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V] (M : Submodule R V)
    (hM : Submodule.span K (M : Set V) = ⊤) (v : V) : ∃ s ∈ nonZeroDivisors R, s • v ∈ M := by
  have hv : v ∈ Submodule.span K (M : Set V) := by rw [hM]; trivial
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_mem _, by rwa [one_smul]⟩
  | zero => exact ⟨1, one_mem _, by rw [smul_zero]; exact M.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨t, ht, hty⟩ := hy
    refine ⟨s * t, mul_mem hs ht, ?_⟩
    have h1 : (s * t) • x = t • (s • x) := by rw [mul_comm, mul_smul]
    rw [smul_add, h1, mul_smul]
    exact M.add_mem (M.smul_mem _ hsx) (M.smul_mem _ hty)
  | smul a x _ hx =>
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨n, d, hd, rfl⟩ := IsFractionRing.div_surjective R a
    refine ⟨d * s, mul_mem hd hs, ?_⟩
    have hd0 : algebraMap R K d ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr (nonZeroDivisors.ne_zero hd)
    have h1 : (d * s) • ((algebraMap R K n / algebraMap R K d) • x) = n • (s • x) := by
      rw [← algebraMap_smul K (d * s), ← algebraMap_smul K n, ← algebraMap_smul K s, smul_smul, smul_smul, map_mul]
      congr 1
      field_simp
    rw [h1]
    exact M.smul_mem _ hsx

theorem finrank_quot_eq {R K V : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V] (M : Submodule R V)
    (hM : Submodule.span K (M : Set V) = ⊤) (W : Submodule K V) :
    finrank R (M ⧸ (W.restrictScalars R).comap M.subtype) = finrank K (V ⧸ W) := by
  let g : M →ₗ[R] (V ⧸ W) := (W.mkQ.restrictScalars R).comp M.subtype
  have hker : LinearMap.ker g = (W.restrictScalars R).comap M.subtype := by
    ext x
    simp [g]
  let f : (M ⧸ (W.restrictScalars R).comap M.subtype) →ₗ[R] (V ⧸ W) :=
    Submodule.liftQ _ g (le_of_eq hker.symm)
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ (le_of_eq hker)
  have hloc : IsLocalizedModule (nonZeroDivisors R) f := by
    refine ⟨fun s => ?_, fun y => ?_, fun {x₁ x₂} h => ⟨1, by rw [hinj h]⟩⟩
    · have hs0 : algebraMap R K s ≠ 0 :=
        (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr (nonZeroDivisors.ne_zero s.2)
      rw [Module.End.isUnit_iff]
      constructor
      · intro a b hab
        simp only [Module.algebraMap_end_apply] at hab
        rw [← algebraMap_smul K (s : R) a, ← algebraMap_smul K (s : R) b] at hab
        exact smul_right_injective _ hs0 hab
      · intro a
        refine ⟨(algebraMap R K s)⁻¹ • a, ?_⟩
        simp only [Module.algebraMap_end_apply]
        rw [← algebraMap_smul K (s : R), smul_smul, mul_inv_cancel₀ hs0, one_smul]
    · obtain ⟨v, rfl⟩ := W.mkQ_surjective y
      obtain ⟨s, hs, hsv⟩ := exists_den (K := K) M hM v
      refine ⟨(Submodule.Quotient.mk ⟨s • v, hsv⟩, ⟨s, hs⟩), ?_⟩
      rfl
  rw [IsLocalization.finrank_eq K (nonZeroDivisors R) le_rfl, IsLocalizedModule.finrank_eq (nonZeroDivisors R) f le_rfl]

theorem exists_sub_basis {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (Sh : Finset V) (hS : Submodule.span K (Sh : Set V) = ⊤) (W : Submodule K V) :
    ∃ e : Fin (finrank K (V ⧸ W)) → V, (∀ i, e i ∈ Sh) ∧ Submodule.span K (Set.range e) ⊔ W = ⊤ := by
  classical
  obtain ⟨b, hb, hspan, hli⟩ := exists_linearIndependent K (W.mkQ '' (Sh : Set V))
  have htop : Submodule.span K b = ⊤ := by
    rw [hspan, Submodule.span_image, hS, Submodule.map_top, Submodule.range_mkQ]
  have hfin : Finite b := ((Sh.finite_toSet.image _).subset hb).to_subtype
  have := Fintype.ofFinite b
  let bs : Basis b K (V ⧸ W) := Basis.mk hli (by rw [Subtype.range_coe, htop])
  have hcard : Fintype.card b = finrank K (V ⧸ W) := (finrank_eq_card_basis bs).symm
  let eq : Fin (finrank K (V ⧸ W)) ≃ b := (Fintype.equivFinOfCardEq hcard).symm
  have hpre : ∀ k, ∃ v ∈ (Sh : Set V), W.mkQ v = (eq k : V ⧸ W) := fun k => hb (eq k).2
  choose e he1 he2 using hpre
  refine ⟨e, fun i => he1 i, ?_⟩
  rw [sup_comm, ← Submodule.map_mkQ_eq_top, Submodule.map_span, ← Set.range_comp]
  have : (⇑W.mkQ ∘ e) = (Subtype.val : b → V ⧸ W) ∘ eq := by funext k; exact he2 k
  rw [this, Set.range_comp, eq.surjective.range_eq, Set.image_univ, Subtype.range_coe, htop]

end LinAlgQ

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

theorem rhoP_eq_finrank (B : WeightFamilies.Prov D) (CR T c : ℝ) (j : ℕ) (ka : WeightFamilies.Wt D j)
    (hM : Submodule.span B.KO (B.Mlat j ka : Set (B.Cusp j ka)) = ⊤) :
    WeightFamilies.rhoP B CR T c j ka = finrank B.KO (B.Cusp j ka ⧸ WeightFamilies.MggK B CR T c j ka) :=
  finrank_quot_eq (B.Mlat j ka) hM (WeightFamilies.MggK B CR T c j ka)

theorem exists_global_family_quotient_bounded {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j} (G0 : GlobalFamilyData X ka wL wF) (large₂ : SizeData₂ D) (S : Scal B)
    (CRm : ℝ) (T : ℕ) (c be Ch Ah : ℝ)
    (hS4 : ShortG X ka (X.Thc S.sK ka) be)
    (hM : X.Thc S.sK ka ≤ B.Mlat j ka)
    (hbe : be ≤ WeightFamilies.PPv D large₂ Ch Ah * ka.size) :
    ∃ th : Fin (WeightFamilies.rhoP B CRm T c j ka) → B.Mlat j ka,
      ({ G0 with rq := WeightFamilies.rhoP B CRm T c j ka, th := th } : GlobalFamilyData X ka wL wF).TiedQ large₂ S CRm T c Ch Ah := by
  obtain ⟨Sh, hSh, hspan, hshort⟩ := hS4
  have hMtop : Submodule.span B.KO (B.Mlat j ka : Set (B.Cusp j ka)) = ⊤ :=
    top_le_iff.mp (hspan ▸ Submodule.span_mono fun x hx => hM (hSh hx))
  have hex := exists_sub_basis Sh hspan (WeightFamilies.MggK B CRm T c j ka)
  rw [← rhoP_eq_finrank B CRm T c j ka hMtop] at hex
  obtain ⟨e, he, hsup⟩ := hex
  exact ⟨fun i => ⟨e i, hM (hSh (he i))⟩, rfl, fun i => hSh (he i), hsup, fun i => (hshort _ (he i)).trans hbe⟩

theorem exists_global_family_quotient {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j} (G0 : GlobalFamilyData X ka wL wF) (large₂ : SizeData₂ D) (S : Scal B)
    (CRm : ℝ) (T : ℕ) (c Gc Ch Ah : ℝ)
    (hS4 : ShortG X ka (X.Thc S.sK ka) (Gc * ka.size))
    (hM : X.Thc S.sK ka ≤ B.Mlat j ka)
    (hG : Gc ≤ WeightFamilies.PPv D large₂ Ch Ah) :
    ∃ (rq : ℕ) (th : Fin rq → B.Mlat j ka),
      ({ G0 with rq := rq, th := th } : GlobalFamilyData X ka wL wF).TiedQ large₂ S CRm T c Ch Ah :=
  ⟨_, exists_global_family_quotient_bounded G0 large₂ S CRm T c (Gc * ka.size) Ch Ah hS4 hM
    (mul_le_mul_of_nonneg_right hG (by linarith [ka.one_le_size]))⟩

section Unchanged

variable {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j} (G0 : GlobalFamilyData X ka wL wF) (rq : ℕ) (th : Fin rq → B.Mlat j ka)

example : ({ G0 with rq := rq, th := th } : GlobalFamilyData X ka wL wF) =
    ⟨G0.N, G0.w, G0.del, G0.th', G0.rz, G0.alz, G0.th0, G0.zc, rq, th, G0.iet, G0.et, G0.mx⟩ := rfl

theorem tiedW_reQ (S : Scal B) (Gc Prw : ℝ) :
    ({ G0 with rq := rq, th := th } : GlobalFamilyData X ka wL wF).TiedW S Gc Prw ↔ G0.TiedW S Gc Prw := Iff.rfl

theorem tiedTh_reQ (S : Scal B) (Gc : ℝ) :
    ({ G0 with rq := rq, th := th } : GlobalFamilyData X ka wL wF).TiedTh S Gc ↔ G0.TiedTh S Gc := Iff.rfl

theorem tiedZ_reQ (S : Scal B) (T : ℕ) (Gc : ℝ) :
    ({ G0 with rq := rq, th := th } : GlobalFamilyData X ka wL wF).TiedZ S T Gc ↔ G0.TiedZ S T Gc := Iff.rfl

theorem tiedEt_reQ (large₂ : SizeData₂ D) (Cf Af : ℝ) :
    ({ G0 with rq := rq, th := th } : GlobalFamilyData X ka wL wF).TiedEt large₂ Cf Af ↔ G0.TiedEt large₂ Cf Af := Iff.rfl

theorem inBasis_reQ (la : HeightOneSpectrum (𝓞 B.KO)) :
    InBasis ({ G0 with rq := rq, th := th } : GlobalFamilyData X ka wL wF) la ↔ InBasis G0 la := Iff.rfl

theorem inContainZ_reQ (la : HeightOneSpectrum (𝓞 B.KO)) (S : Scal B) (T : ℕ) :
    InContainZ ({ G0 with rq := rq, th := th } : GlobalFamilyData X ka wL wF) la S T ↔ InContainZ G0 la S T := Iff.rfl

theorem inContainM_reQ (la : HeightOneSpectrum (𝓞 B.KO)) (CRm : ℝ) (T : ℕ) (c : ℝ) :
    InContainM ({ G0 with rq := rq, th := th } : GlobalFamilyData X ka wL wF) la CRm T c ↔ InContainM G0 la CRm T c := Iff.rfl

theorem combBound_reQ (S : Scal B) (c : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) :
    CombBound ({ G0 with rq := rq, th := th } : GlobalFamilyData X ka wL wF) S c nus ↔ CombBound G0 S c nus := Iff.rfl

example (la : HeightOneSpectrum (𝓞 B.KO)) :
    PtsG ({ G0 with rq := rq, th := th } : GlobalFamilyData X ka wL wF) la = PtsG G0 la := rfl

def LocalPointData.reQ {G0 : GlobalFamilyData X ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)} (Q : LocalPointData G0 la) (rq : ℕ) (th : Fin rq → B.Mlat j ka) :
    LocalPointData ({ G0 with rq := rq, th := th } : GlobalFamilyData X ka wL wF) la :=
  ⟨Q.y, Q.g0, Q.c⟩

variable {G0} {la : HeightOneSpectrum (𝓞 B.KO)} (Q : LocalPointData G0 la)

theorem LocalPointData.inCurve_reQ : (Q.reQ rq th).InCurve ↔ Q.InCurve := Iff.rfl

theorem LocalPointData.inTie_reQ (S : Scal B) : (Q.reQ rq th).InTie S ↔ Q.InTie S := Iff.rfl

theorem LocalPointData.inLift_reQ (T : ℕ) : (Q.reQ rq th).InLift T ↔ Q.InLift T := Iff.rfl

theorem heights_reQ (Qf : ∀ la, LocalPointData G0 la) (Gc PH Prw Pet : ℝ) :
    Heights (fun la => (Qf la).reQ rq th) Gc PH Prw Pet ↔ Heights Qf Gc PH Prw Pet := Iff.rfl

end Unchanged

end Formalism.MainNotions.Gaps.EtaleWeightGaps
