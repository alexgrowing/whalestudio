import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLocalHomOfNatCast
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CMTypeEmbeddings
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsXdAllIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadTw
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistSecondStepKeptWithLocalisationsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisSideStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodCuspidalParameterLocalSideStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharpolyFinOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeqRationalDataOfEigenStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.RowTriple.Lay

open GlobalTheory.TwInputs Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting.FitRho

theorem exists_heq_of_eq {F : D7 → Sort _} {D₁ D₂ : D7} (h : D₁ = D₂) (x : F D₁) : ∃ y : F D₂, HEq y x := by
  subst h; exact ⟨x, HEq.rfl⟩

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem readTw_withLoc (hL : GlobalTheory.Published.LocalLanglandsGL) (D' : D7) (b : NBuilt hL D') (a : (withLoc b.L).nd.Loc) :
    ReadTw (withLoc b.L) a := by
  have hpq : (withLoc b.L).ntw.l ((withLoc b.L).ntw.twOf a) = (withLoc b.L).nd.l a := (withLoc b.L).ntw.twOf_l a
  refine ⟨(castQ hpq).symm.toRingHom.comp (((withLoc b.L).naut.iotaQ a).comp
      (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap ((withLoc b.L).ntw.twist₂ a) (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.twO_inj (withLoc b.L).ntw a))),
    (castQ hpq).trans ((withLoc b.L).naut.iotaQC a), ?_, ?_, ?_⟩
  · intro z
    obtain ⟨z', hz⟩ := exists_heq hpq z
    show (castQ hpq).symm ((withLoc b.L).naut.iotaQ a (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap _ _ (algebraMap ((withLoc b.L).ntw.O0 ((withLoc b.L).ntw.twOf a)) (FractionRing ((withLoc b.L).ntw.O0 ((withLoc b.L).ntw.twOf a))) (algebraMap ℤ_[((withLoc b.L).ntw.l ((withLoc b.L).ntw.twOf a))] ((withLoc b.L).ntw.O0 ((withLoc b.L).ntw.twOf a)) z)))) = _
    rw [GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap_alg]
    erw [b.Sp.twO_alg a z z' hz, (withLoc b.L).naut.iotaQ_alg a z']
    exact castQ_alg hpq z z' hz
  · intro x
    show (withLoc b.L).naut.iotaQC a ((castQ hpq) ((castQ hpq).symm ((withLoc b.L).naut.iotaQ a (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap _ _ _)))) = _
    have hemb : ∀ x : ↥b.D.LL0, GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap ((withLoc b.L).ntw.twist₂ a) (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.twO_inj (withLoc b.L).ntw a)
        ((if (withLoc b.L).ntw.twSide a then (withLoc b.L).ntw.emb0 ((withLoc b.L).ntw.twOf a) else (withLoc b.L).ntw.emb0b ((withLoc b.L).ntw.twOf a)) x) =
        (withLoc b.L).nd.embK a (x : b.D.what₂.LL) :=
      fracMap_eq ((withLoc b.L).ntw.twist₂ a) _ (if (withLoc b.L).ntw.twSide a then (withLoc b.L).ntw.emb0 ((withLoc b.L).ntw.twOf a) else (withLoc b.L).ntw.emb0b ((withLoc b.L).ntw.twOf a))
        (((withLoc b.L).nd.embK a).comp (algebraMap ↥b.D.LL0 b.D.what₂.LL)) (fun x y hy => (withLoc b.L).ntw.twO_emb a x y hy)
    rw [RingEquiv.apply_symm_apply, hemb x]
    exact (withLoc b.L).naut.iota_LL a _
  · intro y
    show (withLoc b.L).naut.iotaQC a ((castQ hpq) ((castQ hpq).symm ((withLoc b.L).naut.iotaQ a (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap _ _ (algebraMap _ _ y))))) = _
    rw [RingEquiv.apply_symm_apply, GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap_alg]
    rfl

end GlobalTheory.RowTriple.Lay

namespace GlobalTheory.RowTriple.Lay

open GlobalTheory.TwInputs Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting.FitRho

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem sideB_built (hL : GlobalTheory.Published.LocalLanglandsGL) (D' : D7) (b : NBuilt hL D')
    (ψ : D'.nd.Loc → NC.HC D'.host.E) (hψ : ∀ a, NC.ReadC D'.nd.plOm.1 (D'.ntw.psiL a) (NC.iotaC D' a) (ψ a) 0)
    (cf : CharFrame D') (hcf : HEq cf (cfL b.L b.cf))
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D'.host.E)) → PlE D'.host) (hPq : HEq Pq b.Pq)
    (S : RatDat D'.ntw) (hS : HEq S (ratL b.L b.S))
    (hL' : ∀ j, ℕ → PlE D'.host → Module.End D'.what₂.LL (S.WL j)) (hhL : HEq hL' b.hL)
    (eig : ℕ → D'.what₂.FT → ℕ → PlE D'.host → ↥D'.LL0) (heig : HEq eig b.eig)
    (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D'.host.g kk)) →* (↥D'.LL0)ˣ) (hθ : HEq θ b.θ) :
    ∃ Rw : RowSide D', HEq Rw.locR b.A.row.locR ∧ Nonempty (SideB D' cf Rw b.low Pq S hL' eig θ) ∧
      (∀ a σ v, IsSplitPl D'.host v → D'.naut.locW a σ v = Rw.locR σ v) := by
  obtain ⟨D, cf0, jE, A, cg, au, rep, row, low, Pq0, S0, hL0, eig0, θ0, Bs, M, C, tp, ch, mt, big, L, Sp, Au, ss, eq⟩ := b
  subst eq
  obtain rfl := eq_of_heq hcf
  obtain rfl := eq_of_heq hPq
  obtain rfl := eq_of_heq hS
  obtain rfl : hL0 = hL' := (eq_of_heq hhL).symm
  obtain rfl : eig0 = eig := (eq_of_heq heig).symm
  obtain rfl : θ0 = θ := (eq_of_heq hθ).symm
  obtain ⟨Rw, hRw, Bs', -⟩ := GlobalTheory.T.twist_second_step_kept_with_localisations D cf0 A.row low Pq S0 hL0 eig0 θ0 Bs L ψ hψ
  refine ⟨Rw, hRw, ⟨Bs'⟩, fun a σ v _ => ?_⟩
  have e : Rw.locR = A.row.locR := eq_of_heq hRw
  rw [e]
  exact Au.locW a σ v

set_option maxHeartbeats 4000000 in

theorem ks_built (hL : GlobalTheory.Published.LocalLanglandsGL) (D' : D7) (b : NBuilt hL D') (S : RatDat D'.ntw)
    (hS : HEq (ratL b.L b.S) S) (h : ∀ j, 1 ≤ j → j ≤ b.D.R.m → (b.S.A j).IsKsForm) :
    ∀ j, 1 ≤ j → j ≤ D'.R.m → (S.A j).IsKsForm := by
  obtain ⟨D, cf0, jE, A, cg, au, rep, row, low, Pq0, S0, hL0, eig0, θ0, Bs, M, C, tp, ch, mt, big, L, Sp, Au, ss, eq⟩ := b
  subst eq
  obtain rfl := eq_of_heq hS
  exact h

end GlobalTheory.RowTriple.Lay

namespace GlobalTheory.RowTriple.Lay

open GlobalTheory.TwInputs Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting.FitRho

theorem heq_cf_of_pack {p q : Σ (D₁ : D7) (c₁ : CharFrame D₁) (C₁ : NChoice D₁), TupTied D₁ c₁ C₁} (h : p = q) :
    HEq p.2.1 q.2.1 := by
  subst h; rfl

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem layer_inputs_atMem : PrN → SerN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL fun _ _ _ _ w Z _ _ t nch n c => ∃ (cf : CharFrame (w.D Z)) (Rw : RowSide (w.D Z)) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield (w.D Z).host.E)) → PlE (w.D Z).host) (S : RatDat (w.D Z).ntw) (hL' : ∀ j, ℕ → PlE (w.D Z).host → Module.End (w.D Z).what₂.LL (S.WL j)) (eig : ℕ → (w.D Z).what₂.FT → ℕ → PlE (w.D Z).host → ↥(w.D Z).LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod ((w.D Z).host.g kk)) →* (↥(w.D Z).LL0)ˣ) (_ : SideB (w.D Z) cf Rw low Pq S hL' eig θ) (Sb : Finset (PlE (w.D Z).host)), (∀ i, Sb ⊆ (w.D Z).ntw.S0 i) ∧ (∀ j, 1 ≤ j → j ≤ (w.D Z).R.m → (S.A j).IsKsForm) ∧ GlobalTheory.TwInputs.EigTrue (w.D Z) cf Rw Sb eig ∧ GlobalTheory.TwInputs.EigOcc (w.D Z) S θ hL' Sb eig ∧ GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.GoodRowCuspParam (w.D Z) Rw ∧ (w.D Z).nexp.sig_all ∧ (∀ a σ v, IsSplitPl (w.D Z).host v → (w.D Z).naut.locW a σ v = Rw.locR σ v) ∧ ∀ a, GlobalTheory.RowTriple.ReadTw (w.D Z) a := by
  intro hP hS hL
  refine GlobalTheory.HeightCounting.Up.Model.AtMem.imp (GlobalTheory.HeightCounting.Up.Model.AtMem.and (GlobalTheory.HeightCounting.Up.Model.AtMem.and (GlobalTheory.T.exists_galois_side hP hS hL)
    (GlobalTheory.T.good_cuspidal_parameter_local_side hP hL)) (GlobalTheory.T.heq_rational_data_of_eigen hP hS hL))
    fun K B f T w Z Wt p0 t nch n c h => ?_
  obtain ⟨⟨⟨G, -, -, -⟩, hpar⟩, heigH⟩ := h
  have hcf : HEq (TC.cf w.I w.l Z) (cfL c.a.nt.L c.a.nt.cf) := heq_cf_of_pack c.a.nt.pack
  obtain ⟨eig, heig⟩ := exists_heq_of_eq (F := fun D : D7 => ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) c.a.nt.eq.symm
    c.a.nt.eig
  obtain ⟨θ, hθ⟩ := exists_heq_of_eq (F := fun D : D7 => ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ)
    c.a.nt.eq.symm c.a.nt.θ
  obtain ⟨Rw, hRw, ⟨Bs⟩, hloc⟩ := sideB_built hL (w.D Z) c.a.nt.toNBuilt c.a.all.chiD.psi c.a.all.chi.psi (TC.cf w.I w.l Z) hcf
    c.a.Pq c.a.Pq_eq.symm _ c.row.S_eq.symm c.row.hecke.hL c.row.hL_eq.symm
    eig heig θ hθ
  obtain ⟨Sb, hSb, hET⟩ := heigH _ c.row.hecke.hL eig θ c.row.S_eq.symm c.row.hL_eq.symm heig hθ
  obtain ⟨hT, hO⟩ := hET Rw hRw
  have hR : ∀ a, ReadTw (withLoc c.a.nt.L) a := readTw_withLoc hL _ c.a.nt.toNBuilt
  rw [← c.a.nt.eq] at hR
  exact ⟨TC.cf w.I w.l Z, Rw, c.a.nt.low, c.a.Pq, _, c.row.hecke.hL, eig, θ, Bs, Sb, hSb,
    ks_built hL (w.D Z) c.a.nt.toNBuilt _ c.row.S_eq c.a.ratIn.ks, hT, hO, hpar Rw hRw,
    GlobalTheory.Triple.IsTripleOf.sig_all G.triple, hloc, hR⟩

end GlobalTheory.RowTriple.Lay
