import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsDpstFrobeniusEigenvectorOfCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTopologicalClosureZpowersSupInertia
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published UpperTheory.V.W
open GlobalTheory.Pst GlobalTheory.TripleGal Module
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

private theorem abs_eig {L D : Type} [Field L] [AddCommGroup D] [Module L D] (U : (End L D)ˣ) (φ g : End L D)
    (hU : (U : End L D) = φ) (hc : φ * g = g * φ) (x : D) (hx0 : x ≠ 0) (s : L) (a b : ℕ) (k : ℤ)
    (hk : k = (b : ℤ) + -(a : ℤ)) (key : g ((φ ^ b) x) = s • (φ ^ a) x) :
    ∃ x' : D, x' ≠ 0 ∧ ∀ n : ℕ, (g * ((U ^ k : (End L D)ˣ) : End L D)) ((φ ^ n) x') = s • (φ ^ n) x' := by
  subst hU hk
  have k0 : g * ((U ^ ((b : ℤ) + -(a : ℤ)) : (End L D)ˣ) : End L D) * (U : End L D) ^ a = g * (U : End L D) ^ b := by
    rw [zpow_add, zpow_neg, zpow_natCast, zpow_natCast, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val,
      mul_assoc, ← Units.val_mul, inv_mul_cancel_right]
  refine ⟨((U : End L D) ^ a) x, fun h0 => hx0 ?_, fun n => ?_⟩
  · exact ((End.isUnit_iff _).1 (U.isUnit.pow a)).1 (h0.trans (map_zero _).symm)
  · have hc' : Commute (g * ((U ^ ((b : ℤ) + -(a : ℤ)) : (End L D)ˣ) : End L D)) ((U : End L D) ^ n) :=
      (Commute.mul_left hc.symm (Commute.units_zpow_right (Commute.refl _) _).symm).pow_right n
    rw [← End.mul_apply, hc'.eq, End.mul_apply, ← End.mul_apply _ _ x, k0, End.mul_apply, key, map_smul]

private theorem eig_of_frob {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ}
    [Fact l.Prime] (P : LocPrime l) {A : ValuationSubring Ω} {w : Plc F} (h : IsPlaceOver A w) {O : Type} [CommRing O]
    [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (hj : GlobalTheory.Pst.Induces Bw)
    (ι : Qbar l ≃+* ℂ) {L : FinExt l} {V : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V]
    [IsScalarTower ℚ_[l] ↥L.1 V] [FiniteDimensional ↥L.1 V] (ρ : Representation ↥L.1 ↥(GK Bw.Kw) V)
    (h1 : finrank ↥L.1 V = 1) (hV : IsPst P ρ) (x : ↥(Dpst P ρ)) (hx0 : x ≠ 0) (σ : Weil h) (s : ↥L.1) {a b : ℕ}
    (hσ : ActsAs A (normV w) (σ : G F Ω) a b)
    (key : actD P ρ (weilToGK Bw h σ) ((phiD P ρ ^ (resDeg l w * b)) x) = s • (phiD P ρ ^ (resDeg l w * a)) x) :
    ι (s : Om l) ∈ (wdPst P ι Bw h hj ρ).eig σ := by
  have hfin := hV.finite
  have e1 : -alpha l σ = ((resDeg l w * b : ℕ) : ℤ) + -((resDeg l w * a : ℕ) : ℤ) := by
    rw [alpha, deg_eq hσ]; push_cast; ring
  obtain ⟨x', hx'0, k1⟩ := abs_eig (phiU P ρ) (phiD P ρ) (actD P ρ (weilToGK Bw h σ)) rfl (phiD_actD P ρ _) x hx0 s
    _ _ _ e1 key
  obtain ⟨n, hn⟩ : ∃ n : ℕ, wdMk P ι ρ ((phiD P ρ ^ n) x') ≠ 0 := by
    by_contra hc
    exact hx'0 (GlobalTheory.PstFaithful.eq_zero_of_wdMk_phiD_pow l P ι _ L _ _ _ fun n => not_not.1 fun hn => hc ⟨n, hn⟩)
  exact ParamAboveModel.mem_eig_wdPst P ι Bw h hj ρ _ h1 hV hn σ s (k1 n)

theorem UpperTheory.V.Loc.wdPotUnr :
    ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {w : Plc F} (h : IsPlaceOver A w) {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (hj : GlobalTheory.Pst.Induces Bw) (ι : Qbar l ≃+* ℂ) (ψ : ↥(Dec (F := F) A) →* (Qbar l)ˣ), Continuous ψ → IsSmooth (ψ.comp (Subgroup.inclusion (Weil_le_Dec h))) → GlobalTheory.Pst.IsPstAt (UpperTheory.V.Loc.PP l) Bw (GlobalTheory.TripleGal.rk1 ψ) → ∀ σ : Weil h, ι (ψ (Subgroup.inclusion (Weil_le_Dec h) σ) : Qbar l) ∈ (GlobalTheory.Pst.wdAt (UpperTheory.V.Loc.PP l) ι Bw h hj (GlobalTheory.TripleGal.rk1 ψ)).eig σ := by
  intro F Ω _ _ _ _ _ l _ A w h O _ _ _ Bw hj ι ψ hψ hs hr σ
  obtain ⟨T⟩ := UpperTheory.V.Loc.tiedP l
  obtain ⟨L, r', hM, hV, e⟩ := wdAt_of_isPstAt ι Bw h hj hr
  rw [e]
  let m : ↥(GK Bw.Kw) →* (↥L.1)ˣ := (Matrix.GeneralLinearGroup.det.comp r').comp Bw.e.symm.toMonoidHom
  have hm0 : ∀ g, (m g : ↥L.1) = (r' (Bw.e.symm g) : Matrix (Fin 1) (Fin 1) ↥L.1) 0 0 := fun g => by
    simp [m, Matrix.det_unique]
  have hm : ∀ g, ((m g : ↥L.1) : Om l) = ψ (Bw.e.symm g) := fun g => by
    have := congrArg (fun f : ↥(Dec (F := F) A) →* GL (Fin 1) (Om l) =>
      (f (Bw.e.symm g) : Matrix (Fin 1) (Fin 1) (Om l)) 0 0) hM.2
    rw [hm0]
    simpa [Formalism.MainNotions.N.mapRep, rk1] using this
  have hρ : ∀ g v, Bw.repE L r' g v = (m g : ↥L.1) • v := fun g v => by
    ext i
    fin_cases i
    simp [LocBridge.repE, hm0, Matrix.mulVec, dotProduct]
  obtain ⟨V, hV1, hV2⟩ := isOpen_induced_iff.1 hs
  have ho2 : IsOpen {g : GK Bw.Kw | ((Bw.e.symm g : Dec (F := F) A) : G F Ω) ∈ V} :=
    hV1.preimage (continuous_subtype_val.comp Bw.e_symm_cont)
  obtain ⟨U, hU, hU'⟩ := isOpen_induced_iff.1 ho2
  have h1 : (1 : GQ l) ∈ U := by
    have h0 : (1 : Ine (F := F) A) ∈ Subtype.val ⁻¹' V := by rw [hV2]; simp
    have : (1 : GK Bw.Kw) ∈ Subtype.val ⁻¹' U := by rw [hU']; simpa using h0
    exact this
  obtain ⟨K', hK1, hK2⟩ := (krullTopology_mem_nhds_one_iff _ _ U).1 (hU.mem_nhds h1)
  obtain ⟨x, hx0, hx⟩ := UpperTheory.exists_dpst_frobenius_eigenvector_of_character _ _ T Bw.Kw (supExt Bw.Kw ⟨K', hK1⟩) L le_sup_left m (Bw.repE L r') hρ
    (by simp only [hm]; exact Units.continuous_val.comp (hψ.comp Bw.e_symm_cont))
    (fun g hg hg' => by
      have h2 : g ∈ Subtype.val ⁻¹' U := hK2 (GK_le (K := ⟨K', hK1⟩) le_sup_right hg)
      rw [hU'] at h2
      have h3 : ((Bw.e.symm g : Dec (F := F) A) : G F Ω) ∈ Ine (F := F) A := by
        refine actsAs_zero_iff (q := 2).1 ⟨(Bw.e.symm g).2, fun y hy => ?_⟩
        rw [hj.valuation_lt_one_iff]
        simp only [pow_zero, pow_one]
        rw [map_sub, ← Bw.e_comm, MulEquiv.apply_symm_apply]
        exact GlobalTheory.FrobGen.norm_sub_lt hg' _ ((hj y).1 ((A.valuation_le_one_iff y).1 hy))
      have h4 : (⟨_, h3⟩ : Ine (F := F) A) ∈ Subtype.val ⁻¹' V := h2
      rw [hV2] at h4
      have h5 : ψ (Bw.e.symm g) = 1 := h4
      refine Units.ext (Subtype.ext ?_)
      rw [hm, h5]
      rfl)
  obtain ⟨a, b, hσ⟩ := σ.2
  have k2 := eig_of_frob (PP l) h Bw hj ι _ (by simp) hV x hx0 σ _ hσ
    (hx (weilToGK Bw h σ) _ _ (weilToGK_frobUr hj σ hσ))
  rw [hm] at k2
  simpa [weilToGK] using k2
