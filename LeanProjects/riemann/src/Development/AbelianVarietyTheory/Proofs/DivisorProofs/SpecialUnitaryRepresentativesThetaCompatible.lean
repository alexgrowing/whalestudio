import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsRestFurther
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialUnitaryLiftInThetaGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteUnitaryPartIsInvertibleUnitaryAdelic
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralAtOfAdelicIntegralAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinCongMemLevEnv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameStabiliserMapsToCompletedLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialUnitaryKottwitzEquivalenceStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.CovTop
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.MassLinkConj
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain
open scoped Matrix

theorem mulVec_mem_hatL {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (Λ : Submodule (𝓞 E) (Fin n → E)) (hβ : Formalism.L2.DIV.IsFrame β Λ)
    (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (hx : x ∈ Formalism.L2.DIV.St β)
    (v : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) (hv : v ∈ Formalism.L2.Herm.hatL (F := F) Λ) :
    x.1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := F) Λ :=
  GlobalTheory.T.frameStabiliser_mapsTo_completedLattice β Λ hβ x hx v hv

theorem sEquiv_of_mul_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (G : Matrix (Fin r) (Fin r) E) (L : Set (Fin r → E))
    (s s' M : Matrix (Fin r) (Fin r) (GlobalTheory.AdLat.RA (maximalRealSubfield E) E)) (γ : Matrix (Fin r) (Fin r) E)
    (hs : GlobalTheory.SUVol.IsSA G s) (hs' : GlobalTheory.SUVol.IsSA G s') (hM : GlobalTheory.UCls.IsKM (IsCMField.complexConj E) G L 1 M)
    (he : s' * M = GlobalTheory.UCls.ratM (maximalRealSubfield E) γ * s) (hγ : γ.det = 1) :
    GlobalTheory.SUVol.SEquiv G L 1 s' s :=
  GlobalTheory.T.special_unitary_kottwitz_equivalence G L s s' M γ hs hs' hM he hγ

theorem isUA_of_neg {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
    (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (k : Matrix (Fin n) (Fin n) (GlobalTheory.AdLat.RA F E))
    (h : GlobalTheory.UCls.IsUA c (-G) k) : GlobalTheory.UCls.IsUA c G k := by
  have e : ∀ x y, GlobalTheory.AdLat.hermA c (-G) x y = -GlobalTheory.AdLat.hermA c G x y := by
    intro x y
    simp only [GlobalTheory.AdLat.hermA, Matrix.neg_apply, TensorProduct.tmul_neg, mul_neg, neg_mul, Finset.sum_neg_distrib]
  refine ⟨h.1, fun x y => ?_⟩
  have := h.2 x y
  rw [e, e] at this
  exact neg_injective this

theorem mulVec_mem_hat (D : D7) {n : ℕ} (β : GL (Fin n) (Formalism.IndefR.Lev.EAf D))
    (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (hβ : Formalism.L2.DIV.IsFrame β Λ)
    (k : GL (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))
    (hk : Formalism.UG.bc (Formalism.IndefR.Lev.swapAE D) k ∈ Formalism.L2.DIV.St β)
    (x : Fin n → Af D.host.F ⊗[D.host.F] D.host.E) (hx : x ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin n → D.host.E))) :
    k.1 *ᵥ x ∈
      GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin n → D.host.E)) := by
  have h1 := GlobalTheory.PrincInLevel.swap_mem_hatL Λ x hx
  have h2 := mulVec_mem_hatL β Λ hβ _ hk _ h1
  have h3 := GlobalTheory.PrincInLevel.swap_symm_mem_hat Λ _ h2
  convert h3 using 1
  funext a
  simp only [Matrix.mulVec, dotProduct, Formalism.UG.bc, Formalism.IndefR.Lev.swapAE, Units.coe_map, MonoidHom.coe_coe,
    RingHom.mapMatrix_apply, Matrix.map_apply, map_sum, map_mul]
  simp

end GlobalTheory.MassLinkConj

namespace GlobalTheory.MassLinkConj
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain
open scoped Matrix

theorem sEquiv_cast {E : Type} [Field E] [NumberField E] [IsCMField E] {n r : ℕ} (h : n = r)
    (J : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E))
    (s s' : Matrix (Fin r) (Fin r) (GlobalTheory.AdLat.RA (maximalRealSubfield E) E))
    (k : Matrix (Fin n) (Fin n) (GlobalTheory.AdLat.RA (maximalRealSubfield E) E)) (γ : Matrix (Fin n) (Fin n) E)
    (hs : GlobalTheory.SUVol.IsSA (Matrix.transpose (J.submatrix (Fin.cast h.symm) (Fin.cast h.symm))) s)
    (hs' : GlobalTheory.SUVol.IsSA (Matrix.transpose (J.submatrix (Fin.cast h.symm) (Fin.cast h.symm))) s')
    (hkU : GlobalTheory.UCls.IsUA (IsCMField.complexConj E) (-Jᵀ) k)
    (hk1 : ∀ x ∈ GlobalTheory.AdLat.hat (maximalRealSubfield E) (Λ : Set (Fin n → E)),
      k *ᵥ x ∈ GlobalTheory.AdLat.hat (maximalRealSubfield E) (Λ : Set (Fin n → E)))
    (hk2 : ∀ x ∈ GlobalTheory.AdLat.hat (maximalRealSubfield E) (Λ : Set (Fin n → E)),
      ∃ y ∈ GlobalTheory.AdLat.hat (maximalRealSubfield E) (Λ : Set (Fin n → E)), k *ᵥ y = x)
    (he : s'.submatrix (Fin.cast h) (Fin.cast h) * k =
      GlobalTheory.UCls.ratM (maximalRealSubfield E) γ * s.submatrix (Fin.cast h) (Fin.cast h))
    (hγ : γ.det = 1) :
    GlobalTheory.SUVol.SEquiv (Matrix.transpose (J.submatrix (Fin.cast h.symm) (Fin.cast h.symm)))
      ((Λ.comap (LinearMap.funLeft (𝓞 E) E (Fin.cast h)) : Submodule (𝓞 E) (Fin r → E)) : Set (Fin r → E)) 1 s' s := by
  subst h
  have eΛ : Λ.comap (LinearMap.funLeft (𝓞 E) E (Fin.cast rfl)) = Λ := by
    ext x; rfl
  have eJ : Matrix.transpose (J.submatrix (Fin.cast (rfl : n = n).symm) (Fin.cast (rfl : n = n).symm)) = Jᵀ := by
    ext a b; rfl
  have es : ∀ t : Matrix (Fin n) (Fin n) (GlobalTheory.AdLat.RA (maximalRealSubfield E) E),
      t.submatrix (Fin.cast rfl) (Fin.cast rfl) = t := fun t => by ext a b; rfl
  rw [eΛ, eJ]
  rw [eJ] at hs hs'
  rw [es, es] at he
  refine sEquiv_of_mul_eq _ _ s s' k γ hs hs' ⟨isUA_of_neg _ _ _ hkU, fun x hx => ⟨k *ᵥ x - x,
    sub_mem (hk1 x hx) hx, by simp⟩, hk2⟩ he hγ

end GlobalTheory.MassLinkConj

namespace GlobalTheory.MassLinkConj
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain
open scoped Matrix

theorem finHom_rat (D : D7) (V : Formalism.BasicNotions.TH.HSp D) (g : Theta.GA D V) (γ : GL (Fin V.rank) D.host.E)
    (hg : Theta.matHom V g = Formalism.UG.bc (GlobalTheoryTheory.GenusMassVolumes.inclR (GlobalTheoryTheory.GenusMassVolumes.AF D.host.F)) γ) :
    (Theta.finHom V g).1 = (γ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map
      (fun e => (1 : Af D.host.F) ⊗ₜ[D.host.F] e) := by
  have : Theta.finHom V g = Formalism.UG.bc (Algebra.TensorProduct.map (sndA D.host.F)
      (AlgHom.id D.host.F D.host.E)).toRingHom (Theta.matHom V g) := rfl
  rw [this, hg]
  ext a b
  simp [Formalism.UG.bc, GlobalTheoryTheory.GenusMassVolumes.inclR]

theorem det_mem_intAf {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (hx : x ∈ Formalism.L2.DIV.St β) : x.1.det ∈ Formalism.L2.Herm.intAf F E := by
  obtain ⟨y, rfl⟩ := hx
  have e : (Formalism.L2.DIV.frGL β y).1.det = (Formalism.L2.DIV.intGL F E n y).1.det := by
    show (β * Formalism.L2.DIV.intGL F E n y * β⁻¹).1.det = _
    rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc, ← Matrix.det_mul,
      Units.inv_mul, Matrix.det_one, one_mul]
  rw [e]
  have e2 : (Formalism.L2.DIV.intGL F E n y).1 = (Formalism.L2.Herm.intAf F E).subtype.mapMatrix y.1 := rfl
  rw [e2, ← RingHom.map_det]
  exact (y.1.det).2

set_option maxHeartbeats 2000000 in

theorem main : ∀ (D : D7) (Tu : Type) (Cl : LevCh D Tu) (t0 : Tu), Cl.Is t0 → ∀ (i : Fin D.R.m), letI : IsCMField D.host.E := D.host.isCMField_hostE; ∀ (J : Type) (s : J → Matrix (Fin D.R.r) (Fin D.R.r) (GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E)), GlobalTheory.SUVol.IsSReps (GlobalTheory.MassLink.gm D i) (GlobalTheory.MassLink.lat Cl i : Set (Fin D.R.r → D.host.E)) 1 s → ∀ (j j' : J) (g : Theta.GA D (Wc D i)) (γ : GL (Fin (Wc D i).rank) D.host.E), g ∈ Theta.GQ (Wc D i) → Theta.matHom (Wc D i) g = Formalism.UG.bc (GlobalTheoryTheory.GenusMassVolumes.inclR (GlobalTheoryTheory.GenusMassVolumes.AF D.host.F)) γ → Formalism.IndefR.Lev.finE (Wc D i) ((GlobalTheory.MassLink.lift D i (s j'))⁻¹ * g * GlobalTheory.MassLink.lift D i (s j)) ∈ GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i (LevelP.full Cl.Pg D.R.r ℂ) → IsIntegral ℤ (γ : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) D.host.E).det ∧ ((γ : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) D.host.E).det = 1 → j = j') := by
  intro D Tu Cl t0 hCl i
  letI : IsCMField D.host.E := D.host.isCMField_hostE
  intro J s hS j j' g γ _ hgm hk
  obtain ⟨-, hl⟩ := GlobalTheory.MassLift.lift_spec D i (s j) (hS.1 j)
  obtain ⟨-, hl'⟩ := GlobalTheory.MassLift.lift_spec D i (s j') (hS.1 j')
  have hfg := finHom_rat D (Wc D i) g γ hgm
  set k := Theta.finHom (Wc D i) ((GlobalTheory.MassLink.lift D i (s j'))⁻¹ * g * GlobalTheory.MassLink.lift D i (s j)) with hkdef
  have hkeq : (Theta.finHom (Wc D i) (GlobalTheory.MassLink.lift D i (s j'))).1 * k.1 =
      (Theta.finHom (Wc D i) g).1 * (Theta.finHom (Wc D i) (GlobalTheory.MassLink.lift D i (s j))).1 := by
    rw [← Units.val_mul, ← Units.val_mul, hkdef, ← map_mul, ← map_mul]
    congr 2
    group
  rw [hl, hl', hfg] at hkeq
  have hSt : Formalism.UG.bc (Formalism.IndefR.Lev.swapAE D) k ∈ Formalism.L2.DIV.St (Cl.βW i) := Formalism.L2.DIV.parLev_St hk.1
  have hfr : Formalism.L2.DIV.IsFrame (Cl.βW i) (Cl.ΛW i) := by obtain ⟨c, h, -⟩ := hCl.βW i; exact h
  have hdet1 : ∀ t : Matrix (Fin D.R.r) (Fin D.R.r) (GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E),
      GlobalTheory.SUVol.IsSA (GlobalTheory.MassLink.gm D i) t → (t.submatrix (Fin.cast (rank_Wc i)) (Fin.cast (rank_Wc i))).det = 1 := by
    intro t ht
    exact (Matrix.det_submatrix_equiv_self (finCongr (rank_Wc i)) t).trans ht.2
  have hdk : k.1.det = (1 : Af D.host.F) ⊗ₜ[D.host.F] γ.1.det := by
    have := congrArg Matrix.det hkeq
    rw [Matrix.det_mul, Matrix.det_mul, hdet1 _ (hS.1 j), hdet1 _ (hS.1 j'), one_mul, mul_one] at this
    rw [this]
    exact (RingHom.map_det (Algebra.TensorProduct.includeRight :
      D.host.E →ₐ[D.host.F] Af D.host.F ⊗[D.host.F] D.host.E).toRingHom _).symm
  refine ⟨?_, fun hγ => ?_⟩
  · have hm := det_mem_intAf _ _ hSt
    have e : (Formalism.UG.bc (Formalism.IndefR.Lev.swapAE D) k).1.det = Formalism.L2.Col.iA D.host.F D.host.E
        γ.1.det := by
      show ((Formalism.IndefR.Lev.swapAE D).mapMatrix k.1).det = _
      rw [← RingHom.map_det, hdk]
      rfl
    rw [e] at hm
    obtain ⟨c, hc⟩ := GlobalTheory.RatInt.mem_range_of_iA_mem _ hm
    rw [← hc]
    exact RingOfIntegers.isIntegral_coe c
  · have hU : GlobalTheory.UCls.IsUA (IsCMField.complexConj D.host.E) (-((Wc D i).gram)ᵀ)
        (k.1 : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) (GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E)) :=
      GlobalTheory.FinUA.isUA_finHom D (Wc D i) _
    have h1 : ∀ x ∈ GlobalTheory.AdLat.hat (maximalRealSubfield D.host.E) (Cl.ΛW i : Set (Fin (Wc D i).rank → D.host.E)),
        (k.1 : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) (GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E)) *ᵥ x ∈
          GlobalTheory.AdLat.hat (maximalRealSubfield D.host.E) (Cl.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) :=
      fun x hx => mulVec_mem_hat D (Cl.βW i) (Cl.ΛW i) hfr k hSt x hx
    have hSt' : Formalism.UG.bc (Formalism.IndefR.Lev.swapAE D) k⁻¹ ∈ Formalism.L2.DIV.St (Cl.βW i) := by
      rw [map_inv]; exact inv_mem hSt
    have h2 : ∀ x ∈ GlobalTheory.AdLat.hat (maximalRealSubfield D.host.E) (Cl.ΛW i : Set (Fin (Wc D i).rank → D.host.E)),
        ∃ y ∈ GlobalTheory.AdLat.hat (maximalRealSubfield D.host.E) (Cl.ΛW i : Set (Fin (Wc D i).rank → D.host.E)),
          (k.1 : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) (GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E)) *ᵥ y = x := by
      intro x hx
      refine ⟨(k⁻¹).1 *ᵥ x, mulVec_mem_hat D (Cl.βW i) (Cl.ΛW i) hfr k⁻¹ hSt' x hx, ?_⟩
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    have he : (s j').submatrix (Fin.cast (rank_Wc i)) (Fin.cast (rank_Wc i)) *
        (k.1 : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) (GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E)) =
        GlobalTheory.UCls.ratM (maximalRealSubfield D.host.E) γ.1 * (s j).submatrix (Fin.cast (rank_Wc i)) (Fin.cast (rank_Wc i)) :=
      hkeq
    have hE := sEquiv_cast (rank_Wc i) (Wc D i).gram (Cl.ΛW i) (s j) (s j') k.1 γ.1 (hS.1 j) (hS.1 j') hU h1 h2 he hγ
    exact (hS.2.1 j' j hE).symm

end GlobalTheory.MassLinkConj
