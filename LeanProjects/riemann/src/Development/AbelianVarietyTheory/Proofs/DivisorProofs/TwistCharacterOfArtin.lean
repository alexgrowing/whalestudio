import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DenseRangeUnits
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterIdeleCharacterMatchUnique

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp GlobalTheory.SeriesTie

namespace GlobalTheory.TwistChr

attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 10000] GlobalTheory.GalChar.isTorsionFree_field

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

theorem hecke_eq_of_frob {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {art : Ideles E →* Gab E Ω} (ha : IsGlobalArtin art) (r : G E Ω →* ℂˣ) (hr : IsOpen (r.ker : Set (G E Ω))) (χ : HChar E)
    (S : Finset (HeightOneSpectrum (𝓞 E))) (hu : ∀ v ∉ S, χ.UnrAt v)
    (hf : ∀ v ∉ S, ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ σ : G E Ω, IsFrob (F := E) A (normV v) σ → r σ = (χ.val v)⁻¹)
    (x : Ideles E) (σ : G E Ω) (hx : art x = toAb E Ω σ) : χ.1 x = r σ := by
  have hc := continuous_of_isOpen_ker' r hr
  have h : (liftAb r hc).comp art * χ.1⁻¹ = 1 := by
    refine GlobalTheory.FrobDense.eq_one_of_away _ (((continuous_liftAb r hc).comp ha.quot.continuous).mul χ.2.1.inv) (fun k => ?_) S
      fun v hv => ?_
    · have hk : diagUnits E k ∈ art.ker := by
        rw [ha.ker]
        exact Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_left ⟨k, rfl⟩)
      rw [MonoidHom.mul_apply, MonoidHom.inv_apply, χ.2.2, MonoidHom.comp_apply, MonoidHom.mem_ker.mp hk, map_one, inv_one, one_mul]
    · refine GlobalTheory.FrobDense.eq_one_of_unif (((liftAb r hc).comp art * χ.1⁻¹).comp (localIdele E v)) fun y hy => ?_
      obtain ⟨A, hA⟩ := exists_isPlaceOver Ω v
      obtain ⟨τ, hτ, e⟩ := (ha.frob v A hA _).mp ⟨y, hy, rfl⟩
      have h1 : χ.1 (localIdele E v y) = χ.val v := χ.val_eq (hu v hv) y hy
      rw [MonoidHom.comp_apply, MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.comp_apply, ← e, liftAb_toAb, map_inv,
        hf v hv A hA τ hτ, inv_inv, h1, mul_inv_cancel]
  have h2 := DFunLike.congr_fun h x
  rw [MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.comp_apply, hx, liftAb_toAb, MonoidHom.one_apply, mul_inv_eq_one] at h2
  exact h2.symm

theorem chrEq_charOf {D : D7} {Ω : Type} [Field Ω] [Algebra D.host.E Ω] [IsAlgClosure D.host.E Ω] {a : Recip D Ω} (ha : a.Good)
    {R : Type} [CommRing R] (f : R →+* ℂ) (ψ : G D.host.E Ω →* Rˣ) (hψ : IsOpen (ψ.ker : Set (G D.host.E Ω))) {n : ℕ} (hn : n ≠ 0)
    (hp : ∀ σ, ψ σ ^ n = 1) (χ : HChar D.host.E) (S : Finset (HeightOneSpectrum (𝓞 D.host.E))) (hu : ∀ v ∉ S, χ.UnrAt v)
    (hf : ∀ v ∉ S, ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ σ : G D.host.E Ω, IsFrob (F := D.host.E) A (normV v) σ →
      f (ψ σ : Rˣ) = (((χ.val v)⁻¹ : ℂˣ) : ℂ)) : ChrEq (charOf a f ψ) χ := by
  have key : ∀ x, ((charOf a f ψ x : Circle) : ℂ) = ((χ.1 (Units.map a.κ.toMonoidHom x) : ℂˣ) : ℂ) := fun x => by
    obtain ⟨σ, hσ⟩ := a.exists_sym x
    rw [charOf_eq a f hψ hσ hn (hp σ), hecke_eq_of_frob ha.artin ((Units.map f.toMonoidHom).comp ψ)
      (Subgroup.isOpen_mono (H₁ := ψ.ker) (fun g hg => by
        rw [MonoidHom.mem_ker] at hg ⊢
        rw [MonoidHom.comp_apply, hg, map_one]) hψ) χ S hu (fun v hv A hA τ hτ => Units.ext (hf v hv A hA τ hτ)) _ σ hσ]
    rfl
  refine ⟨⟨?_, fun k => ?_⟩, fun P e he k x hx => ?_⟩
  · refine continuous_induced_rng.2 ?_
    exact (Units.continuous_val.comp (χ.2.1.comp (Continuous.units_map _ ha.cont))).congr fun x => (key x).symm
  · refine Circle.ext ?_
    rw [key, show Units.map a.κ.toMonoidHom (Units.map (incA D).toMonoidHom k) = diagUnits D.host.E k from Units.ext (ha.rat k), χ.2.2]
    rfl
  · rw [key, show Units.map a.κ.toMonoidHom x = localIdele D.host.E P (atFin P k) from Units.ext (by
      change a.κ (x : AE D) = _
      rw [hx, ha.loc P e he k])]
    rfl

theorem chrEq_mul {D : D7} {c c' : (AE D)ˣ →* Circle} {χ χ' : HChar D.host.E} (h : ChrEq c χ) (h' : ChrEq c' χ') :
    ChrEq (c * c') (χ * χ') := by
  refine ⟨⟨h.1.1.mul h'.1.1, fun x => ?_⟩, fun P e he k x hx => ?_⟩
  · rw [MonoidHom.mul_apply, h.1.2, h'.1.2, one_mul]
  · rw [MonoidHom.mul_apply, Circle.coe_mul, h.2 P e he k x hx, h'.2 P e he k x hx]
    rfl

theorem finite_placesOver (E : Type) [Field E] [NumberField E] {l : ℕ} (hl : l ≠ 0) : (Formalism.BasicNotions.placesOver E l).Finite := by
  have h0 : Ideal.span {((l : ℕ) : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hl
  exact (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr hv

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} {p : PtAt ex Csz} {w : D.what₂.places.Pl}

theorem chrEq_tw (h : RecTies p) (hw : D.what₂.muAt w ≠ D.what₂.mu0)
    (hψ : IntegralHeckeForms.TwOK (ex.nch.twI w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w))
    {ρ : Setup D.ntw} (hρ : ρ.Good) (hA : Adapted p w ρ) :
    ChrEq (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w)).chi (p.Tp.psi w) := by
  classical
  obtain ⟨-, -, hopen, -, hzk, -, -⟩ := hψ
  obtain ⟨-, e, he, he'⟩ := hA
  have hl : D.ntw.l (ex.nch.twI w) ≠ 0 := (D.ntw.lPrime _).out.ne_zero
  have hz : D.ntw.zk (ex.nch.twI w) (ex.nch.k' w) ^ (D.ntw.l (ex.nch.twI w) ^ ex.nch.k' w) = 1 :=
    Units.ext (by simpa using (D.ntw.zk_prim (ex.nch.twI w) (ex.nch.k' w)).pow_eq_one)
  have hfin := finite_placesOver D.host.E (l := D.what₂.places.resChar w) (ex.nch.twI_l w ▸ hl)
  refine chrEq_charOf hρ.rc _ _ hopen (pow_ne_zero (ex.nch.k' w) hl) (fun σ => ?_) _ (ex.nch.Q w ∪ hfin.toFinset)
    (fun v hv => ((p.Tp.psi_is w hw).ram v).2 fun hQ => hv (Finset.mem_union_left _ hQ)) fun v hv A hA σ hσ => ?_
  · obtain ⟨m, hm⟩ := hzk σ
    rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz, one_zpow]
  · obtain ⟨y, hy, hy'⟩ := h.psi_read w hw v (fun hQ => hv (Finset.mem_union_left _ hQ))
      (fun hQ => hv (Finset.mem_union_right _ (hfin.mem_toFinset.2 hQ))) A σ hA hσ
    rw [← he', ← hy', he, hy]

theorem xi_eq (hw : D.what₂.muAt w ≠ D.what₂.mu0) {ρ : Setup D.ntw} (hP : RealPin p.R p.cG ρ) (j : Fin D.R.m) (b : Bool)
    {c : (AE D)ˣ →* Circle} (hc : ChrEq c (p.Tp.psi w)) :
    p.R.xi (p.R.mu (D.plEq w)) = (ρ.B (ex.nch.twI w) j b).de.chi * c := by
  have h1 := p.charW.base.lev.xi (p.R.mu (D.plEq w))
  have h2 : p.R.toRealDat.toLevCh.xiH (p.R.mu (D.plEq w)) = p.R.C.delAt (D.ntw.l (ex.nch.twI w)) * p.Tp.psi w := by
    rw [← p.tupAt w, p.tupXi _ (Or.inr ⟨w, rfl⟩), (D.what₂.muAt_or w).resolve_left hw, p.Tp.xi_tw, ex.nch.twI_l]
  exact GlobalTheory.ChrEqUnique.idc_unique D _ _ _ h1 (h2 ▸ chrEq_mul (hP.delta _ j b) hc)

end Point

theorem twChr_of_twAdm : GlobalTheory.Published.GlobalArtinReciprocity → TwAdm → TwChr := fun _ h =>
  Closed.imp h fun _ _ _ ⟨x0, H⟩ => ⟨x0, fun x hx h0 i p r hm w hw j _ hρ hA =>
    have hw' := (p.tw_iff w).1 hw
    have h1 := chrEq_tw hm.2.2 hw' (H x hx h0 i p r hm w hw j).1 hρ hA
    ⟨h1, xi_eq hw' hA.1 j _ h1⟩⟩

end GlobalTheory.TwistChr

end
