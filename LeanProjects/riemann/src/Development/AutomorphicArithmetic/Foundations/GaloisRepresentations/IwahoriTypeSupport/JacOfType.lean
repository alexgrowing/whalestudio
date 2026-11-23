import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IwahoriTypeSupport.TorusScalar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsJLeviMulJPlus
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IwahoriNeBotOfSpherical
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix UpperTheory.Gal.TypesAndIwahori

theorem UpperTheory.Gal.TypesAndIwahori.jacOfType :
    UpperTheory.Gal.TypesAndIwahori.Loc → UpperTheory.Gal.TypesAndIwahori.JacOfType := by
  intro L k _ _ _ _ N s d e V _ _ π hs hi θ μ hμ ⟨v, hv0, hv⟩
  have hadm : IsAdmissible π := (L.bz k).1 (Fin N) V π hs hi
  have hb := L.mp k N s d e V π hadm
  have hJ : KOne k (Fin N) ⊔ (unipRad k e ⊓ KO k (Fin N)) = proRad k e :=
    (GlobalTheory.LocGL.IwahoriFactor.proRad_eq_sup e).symm
  rw [hJ] at hb
  have key : ∀ g ∈ proRad k e, π g v = v := by
    intro g hg
    have hp : g ∈ parahoric k e := proRad_le_parahoric e hg
    have h1 : parahoricProj k e ⟨g, hp⟩ = 1 := (parahoricProj_eq_one_iff e ⟨g, hp⟩).2 hg
    have h2 : π g v = ((typeChar e θ ⟨g, hp⟩ : ℂˣ) : ℂ) • v := hv ⟨g, hp⟩
    have h3 : typeChar e θ ⟨g, hp⟩ = 1 := by
      show leviChar _ θ (parahoricProj k e ⟨g, hp⟩) = 1
      rw [h1, map_one]
    rw [h2, h3, Units.val_one, one_smul]
  have hfix : v ∈ fixed π (proRad k e) := GlobalTheory.Cong.LimitAtL.mem_fixed.2 key
  have h0 : (0 : V) ∈ fixed π (proRad k e) := zero_mem _
  refine ⟨Submodule.Quotient.mk v, fun hy => hv0 (hb.injOn hfix h0 ?_), fun x hx => ?_⟩
  · simpa using hy
  · have h1 : jacU e π x (Submodule.Quotient.mk v) = Submodule.Quotient.mk (π (leviEmb k e x) v) := rfl
    have h2 := hv ⟨leviEmb k e x, leviEmb_mem_parahoric e ⟨x, hx⟩⟩
    have h3 : π (leviEmb k e x) v = ((typeChar e θ ⟨leviEmb k e x, leviEmb_mem_parahoric e ⟨x, hx⟩⟩ : ℂˣ) : ℂ) • v := h2
    have h4 : ∀ a, ((μ a (GeneralLinearGroup.det (x a)) : ℂˣ) : ℂ) =
        ((θ a (GeneralLinearGroup.det (redLevi k _ ⟨x, hx⟩ a)) : ℂˣ) : ℂ) := by
      intro a
      have h5 := (hμ a).detChar_eq ⟨x a, hx a trivial⟩
      rw [redLevi_apply]
      exact congrArg (fun u : ℂˣ => (u : ℂ)) h5
    have h6 : parahoricProj k e ⟨leviEmb k e x, leviEmb_mem_parahoric e ⟨x, hx⟩⟩ = redLevi k _ ⟨x, hx⟩ :=
      parahoricProj_leviEmb e ⟨x, hx⟩
    rw [h1, h3, typeChar_apply, h6, Units.coe_prod, Submodule.Quotient.mk_smul]
    simp only [h4]
