import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyAllIff
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalInvariantsMatchSemisimple
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NotMemPlacesOverOfNe
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LatticeConditions
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.HeightCounting.FitRho

open Formalism.L2.NR

def castQ {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (h : p = q) : Qbar p ≃+* Qbar q := by
  subst h; exact RingEquiv.refl _

theorem exists_heq {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (h : p = q) (z : ℤ_[p]) : ∃ z' : ℤ_[q], HEq z z' := by
  subst h; exact ⟨z, HEq.rfl⟩

theorem castQ_alg {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (h : p = q) (z : ℤ_[p]) (z' : ℤ_[q]) (hz : HEq z z') :
    (castQ h).symm (algebraMap ℚ_[q] (Qbar q) (z' : ℚ_[q])) = algebraMap ℚ_[p] (Qbar p) (z : ℚ_[p]) := by
  subst h
  obtain rfl := eq_of_heq hz
  rfl

theorem mapRep_mapRep {Γ A B C : Type} [Group Γ] [CommRing A] [CommRing B] [CommRing C] {n : ℕ} (f : A →+* B)
    (g : B →+* C) (ρ : Γ →* GL (Fin n) A) : mapRep g (mapRep f ρ) = mapRep (g.comp f) ρ := by
  ext x i j
  rfl

theorem isRepOf_cast (D : D7) {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (h : p = q) (ι : Qbar q ≃+* ℂ) {n : ℕ}
    (π : D.naut.CG n) (s : ℝ) (ρ : G D.host.E D.nd.Om →* GL (Fin n) (Qbar q))
    (hρ : IsRepOf D p ((castQ h).trans ι) π s (mapRep (castQ h).symm.toRingHom ρ)) : IsRepOf D q ι π s ρ := by
  subst h
  have e1 : (castQ (rfl : p = p)).trans ι = ι := by ext x; rfl
  have e2 : mapRep (castQ (rfl : p = p)).symm.toRingHom ρ = ρ := by ext g i j; rfl
  rw [e1, e2] at hρ
  exact hρ

theorem conj_of_isRepOf (D : D7) {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {n : ℕ} (π : D.naut.CG n) (s : ℝ)
    (hC : GlobalTheory.RowTie.ChebSplit D.nd) (ρ₁ ρ₂ : G D.host.E D.nd.Om →* GL (Fin n) (Qbar l))
    (h₁ : IsRepOf D l ι π s ρ₁) (h₂ : IsRepOf D l ι π s ρ₂) : IsConjRep ρ₁ ρ₂ := by
  obtain ⟨c₁, s₁, f₁⟩ := h₁
  obtain ⟨c₂, s₂, f₂⟩ := h₂
  have hfin := (Filter.eventually_cofinite.mp f₁).union (Filter.eventually_cofinite.mp f₂)
  have hcp := GlobalTheory.TwistLG.charpoly_eq_of_dense ρ₁ ρ₂ c₁ c₂ _ (hC hfin.toFinset).closure_eq (by
    rintro g ⟨w, hw, -, B, hB, hg⟩
    rw [Set.Finite.mem_toFinset] at hw
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hw
    apply Polynomial.map_injective ι.toRingHom ι.injective
    rw [hw.1 B g hB hg, hw.2 B g hB hg])
  obtain ⟨P, hP⟩ := Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix ρ₂ ρ₁ s₂ s₁ (fun g => (hcp g).symm)
  exact ⟨P⁻¹, fun g => by rw [hP g, inv_inv]⟩

theorem charpoly_fin_one {k : Type} [CommRing k] (M : Matrix (Fin 1) (Fin 1) k) : M.charpoly = X - C (M 0 0) := by
  rw [Matrix.charpoly, Matrix.det_unique, Matrix.charmatrix_apply_eq]
  rfl

theorem rhoOfRow_isRepOf (D : D7) (hG : GalRepEx D) (hC : ClassFieldHeckeAlgebraic D) (hη : EtaShiftInt D) (a : D.nd.Loc)
    (π : D.naut.CG D.R.r) (hc : D.naut.csd π) (hr : D.naut.ralg π) :
    IsRepOf D (D.nd.l a) (D.naut.iotaQC a) (D.naut.tw π D.naut.etaTinv) ((1 - (D.R.nV : ℝ)) / 2)
      (rhoOfRow D hG hC hη a π hc hr) := by
  obtain ⟨c1, ss1, f1⟩ := rowRho_spec D hG a π hc hr
  obtain ⟨cχ, awayχ, -⟩ := Classical.choose_spec (hC a D.naut.etaTinv (-(D.R.t : ℝ) / 2) hη)
  set χ1 := Classical.choose (hC a D.naut.etaTinv (-(D.R.t : ℝ) / 2) hη) with hχ1
  have e0 : rhoOfRow D hG hC hη a π hc hr =
      Formalism.MainNotions.SumRepresentations.At.twGL (rowRho D hG a π hc hr) (Matrix.GeneralLinearGroup.det.comp χ1) := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [e0]; exact GlobalTheory.TwistLG.cont_twGL _ _ c1 cχ
  · rw [e0]; exact GlobalTheory.TwistLG.isSSRep_twGL _ _ ss1
  have hfin := placesOver_finite D.host.E (D.nd.l a) (Fact.out : (D.nd.l a).Prime).ne_zero
  filter_upwards [f1, D.naut.locG_unr_ae π, hfin.compl_mem_cofinite] with w hw1 hu hwl
  intro B σ hB hσ
  have hwl' : w ∉ placesOver D.host.E (D.nd.l a) := hwl

  have hue : D.naut.unr (D.naut.lpTw (D.naut.locG D.naut.etaTinv w) (-(D.R.t : ℝ) / 2)) :=
    (D.naut.unr_tw _ _).2 (D.naut.etaTinv_def w).1
  obtain ⟨u, hu1⟩ : ∃ u, D.naut.frobEig (D.naut.lpTw (D.naut.locG D.naut.etaTinv w) (-(D.R.t : ℝ) / 2)) = {u} := by
    apply Multiset.card_eq_one.mp
    rw [D.naut.frobEig_tw _ _ (D.naut.etaTinv_def w).1, Multiset.card_map,
      D.naut.frobEig_card _ (D.naut.etaTinv_def w).1, D.naut.locG_dim]
  have hwd := D.naut.wdOf_frob a χ1 w hwl' cχ (by rw [awayχ w hwl']; exact hue) B σ hB hσ
  rw [awayχ w hwl', hu1, Multiset.map_singleton, Multiset.prod_singleton, charpoly_fin_one, Polynomial.map_sub,
    Polynomial.map_X, Polynomial.map_C] at hwd
  have hχu : D.naut.iotaQC a ((Matrix.GeneralLinearGroup.det.comp χ1 σ : (Qbar (D.nd.l a))ˣ) : Qbar (D.nd.l a)) = u := by
    have := congrArg (Polynomial.coeff · 0) hwd
    simp only [Polynomial.coeff_sub, Polynomial.coeff_X_zero, Polynomial.coeff_C_zero, zero_sub, neg_inj] at this
    show D.naut.iotaQC a ((χ1 σ : Matrix (Fin 1) (Fin 1) _).det) = u
    rw [Matrix.det_unique]
    exact this

  have h1 := hw1 B σ hB hσ
  rw [isoLoc_single] at h1
  rw [e0, GlobalTheory.TwistLG.twGL_val, ← Matrix.charpoly_map, GlobalTheory.ParamRep.map_smul_matrix,
    GlobalTheory.ParamRep.galPol_twist D.nd D.naut π hu u hu1]
  have h2 : ((((rowRho D hG a π hc hr) σ : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) _).map
      (D.naut.iotaQC a).toRingHom).charpoly =
      ((D.naut.frobEig (D.naut.lpTw (D.naut.locG π w) ((1 - (D.R.r : ℝ)) / 2))).map fun α => X - C α).prod := by
    rw [Matrix.charpoly_map]; exact h1
  have h3 := GlobalTheory.ParamRep.charpoly_smul_of_prod _ u _ h2
  have hχu' : (D.naut.iotaQC a).toRingHom ((Matrix.GeneralLinearGroup.det.comp χ1 σ : (Qbar (D.nd.l a))ˣ) :
      Qbar (D.nd.l a)) = u := hχu
  rw [hχu']
  exact h3

end GlobalTheory.HeightCounting.FitRho

namespace GlobalTheory.HeightCounting.FitRho

open Formalism.L2.NR

theorem fracMap_eq {O0 O : Type} [CommRing O0] [IsDomain O0] [ValuationRing O0] [CommRing O] [IsDomain O]
    (f : O0 →+* O) (hf : Function.Injective f) {F : Type} [Field F] (e : F →+* FractionRing O0)
    (e' : F →+* FractionRing O) (h : ∀ x y, algebraMap O0 _ y = e x → e' x = algebraMap O _ (f y)) (x : F) :
    GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap f hf (e x) = e' x := by
  rcases ValuationRing.isInteger_or_isInteger O0 (e x) with ⟨y, hy⟩ | ⟨y, hy⟩
  · rw [← hy, GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap_alg, h x y hy]
  · have hy' : algebraMap O0 (FractionRing O0) y = e x⁻¹ := by rw [map_inv₀]; exact hy
    have h1 := h x⁻¹ y hy'
    have h2 : e x = (algebraMap O0 (FractionRing O0) y)⁻¹ := by rw [hy, inv_inv]
    rw [h2, map_inv₀, GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap_alg, ← h1, map_inv₀, inv_inv]

end GlobalTheory.HeightCounting.FitRho

namespace GlobalTheory.HeightCounting.FitRho

open Formalism.L2.NR

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem rhoS_withLoc (hL : GlobalTheory.Published.LocalLanglandsGL) (D' : D7) (b : NBuilt hL D')
    (hcheb : GlobalTheory.RowTie.ChebSplit b.D.nd) (hP : RowPar (withLoc b.L)) (hG : GalRepEx (withLoc b.L))
    (hC : ClassFieldHeckeAlgebraic (withLoc b.L)) (hη : EtaShiftInt (withLoc b.L)) (a : (withLoc b.L).nd.Loc)
    (s : (withLoc b.L).ntw.Sig ((withLoc b.L).ntw.twOf a))
    (hs : (withLoc b.L).ntw.side _ s = (withLoc b.L).ntw.twSide a) (hj : (withLoc b.L).ntw.jS _ s = (withLoc b.L).nd.j a) :
    ∃ (σ : (withLoc b.L).what₂.FT) (hσ : (withLoc b.L).what₂.isot ((withLoc b.L).nd.j a) σ ≠ ⊥)
      (hg : (withLoc b.L).nd.goodRow σ),
      ∀ (π : (withLoc b.L).naut.CG (withLoc b.L).R.r) (hS : rowSig (withLoc b.L) a σ = [⟨(withLoc b.L).R.r, π, 1⟩]),
        IsConjRep (Formalism.MainNotions.N.mapRep ((Formalism.MainNotions.N.iotaOQ (withLoc b.L).nd (withLoc b.L).naut a).comp ((withLoc b.L).ntw.twist₂ a))
            ((withLoc b.L).ntw.rhoS _ s))
          (rhoOfRow (withLoc b.L) hG hC hη a π (rowSig_csd_ralg (withLoc b.L) hP a σ hσ hg π hS).1
            (rowSig_csd_ralg (withLoc b.L) hP a σ hσ hg π hS).2) := by
  obtain ⟨hiso, hgood, hspec⟩ := b.Bs.rhoS (b.L.T.twOf a) s
  have hσ : (withLoc b.L).what₂.isot ((withLoc b.L).nd.j a) (b.Bs.rowS (b.L.T.twOf a) s) ≠ ⊥ := by
    rw [← hj]; exact hiso
  refine ⟨b.Bs.rowS (b.L.T.twOf a) s, hσ, hgood, fun π hS => ?_⟩
  obtain ⟨hc, hr⟩ := rowSig_csd_ralg (withLoc b.L) hP a _ hσ hgood π hS

  have hloc : ∀ w, IsSplitPl b.D.host w → b.D.naut.locG π w = b.A.row.locR (b.Bs.rowS (b.L.T.twOf a) s) w := by
    intro w hw
    have h1 := (rowSig_spec (withLoc b.L) hP a _ hσ).2.2 w hw
    rw [hS] at h1
    exact ((isoLoc_single (withLoc b.L) π w).symm.trans h1).trans (b.Au.locW a _ w)

  have hpq : (withLoc b.L).ntw.l ((withLoc b.L).ntw.twOf a) = (withLoc b.L).nd.l a := (withLoc b.L).ntw.twOf_l a

  let φ0 : FractionRing ((withLoc b.L).ntw.O0 ((withLoc b.L).ntw.twOf a)) →+* Qbar ((withLoc b.L).nd.l a) :=
    ((withLoc b.L).naut.iotaQ a).comp (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap ((withLoc b.L).ntw.twist₂ a) (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.twO_inj (withLoc b.L).ntw a))
  have hφ0 : φ0.comp (algebraMap ((withLoc b.L).ntw.O0 ((withLoc b.L).ntw.twOf a)) (FractionRing ((withLoc b.L).ntw.O0 ((withLoc b.L).ntw.twOf a)))) =
      (Formalism.MainNotions.N.iotaOQ (withLoc b.L).nd (withLoc b.L).naut a).comp ((withLoc b.L).ntw.twist₂ a) := by
    ext y
    show (withLoc b.L).naut.iotaQ a (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap _ _ (algebraMap _ _ y)) =
      (withLoc b.L).naut.iotaQ a (algebraMap _ _ ((withLoc b.L).ntw.twist₂ a y))
    rw [GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap_alg]
  have hemb : ∀ x : ↥b.D.LL0, GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap ((withLoc b.L).ntw.twist₂ a) (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.twO_inj (withLoc b.L).ntw a)
      ((if (withLoc b.L).ntw.twSide a then (withLoc b.L).ntw.emb0 ((withLoc b.L).ntw.twOf a) else (withLoc b.L).ntw.emb0b ((withLoc b.L).ntw.twOf a)) x) =
      (withLoc b.L).nd.embK a (x : b.D.what₂.LL) :=
    fracMap_eq ((withLoc b.L).ntw.twist₂ a) _ (if (withLoc b.L).ntw.twSide a then (withLoc b.L).ntw.emb0 ((withLoc b.L).ntw.twOf a) else (withLoc b.L).ntw.emb0b ((withLoc b.L).ntw.twOf a))
      (((withLoc b.L).nd.embK a).comp (algebraMap ↥b.D.LL0 b.D.what₂.LL)) (fun x y hy => (withLoc b.L).ntw.twO_emb a x y hy)
  let φ := (castQ hpq).symm.toRingHom.comp φ0
  let ι := (castQ hpq).trans ((withLoc b.L).naut.iotaQC a)
  have hφ : ∀ z : ℤ_[(withLoc b.L).ntw.l ((withLoc b.L).ntw.twOf a)], φ (algebraMap ((withLoc b.L).ntw.O0 ((withLoc b.L).ntw.twOf a)) (FractionRing ((withLoc b.L).ntw.O0 ((withLoc b.L).ntw.twOf a))) (algebraMap ℤ_[(withLoc b.L).ntw.l ((withLoc b.L).ntw.twOf a)] ((withLoc b.L).ntw.O0 ((withLoc b.L).ntw.twOf a)) z)) =
      algebraMap ℚ_[(withLoc b.L).ntw.l ((withLoc b.L).ntw.twOf a)] (Qbar ((withLoc b.L).ntw.l ((withLoc b.L).ntw.twOf a))) (z : ℚ_[(withLoc b.L).ntw.l ((withLoc b.L).ntw.twOf a)]) := by
    intro z
    obtain ⟨z', hz⟩ := exists_heq hpq z
    show (castQ hpq).symm ((withLoc b.L).naut.iotaQ a (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap _ _ (algebraMap ((withLoc b.L).ntw.O0 ((withLoc b.L).ntw.twOf a)) (FractionRing ((withLoc b.L).ntw.O0 ((withLoc b.L).ntw.twOf a))) (algebraMap ℤ_[((withLoc b.L).ntw.l ((withLoc b.L).ntw.twOf a))] ((withLoc b.L).ntw.O0 ((withLoc b.L).ntw.twOf a)) z)))) = _
    rw [GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap_alg]
    erw [b.Sp.twO_alg a z z' hz, (withLoc b.L).naut.iotaQ_alg a z']
    exact castQ_alg hpq z z' hz
  have hι : ∀ x : ↥b.D.LL0, ι (φ ((if (withLoc b.L).ntw.side ((withLoc b.L).ntw.twOf a) s then (withLoc b.L).ntw.emb0 ((withLoc b.L).ntw.twOf a)
      else (withLoc b.L).ntw.emb0b ((withLoc b.L).ntw.twOf a)) x)) = embLL0 b.D x := by
    intro x
    have hs' : (withLoc b.L).ntw.side ((withLoc b.L).ntw.twOf a) s = (withLoc b.L).ntw.twSide a := hs
    rw [hs']
    show (withLoc b.L).naut.iotaQC a ((castQ hpq) ((castQ hpq).symm ((withLoc b.L).naut.iotaQ a (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap _ _ _)))) = _
    rw [RingEquiv.apply_symm_apply, hemb x]
    exact (withLoc b.L).naut.iota_LL a _
  have hR := hspec π hc hr hloc φ ι hφ hι
  have hR' : IsRepOf (withLoc b.L) ((withLoc b.L).ntw.l ((withLoc b.L).ntw.twOf a)) ((castQ hpq).trans ((withLoc b.L).naut.iotaQC a))
      ((withLoc b.L).naut.tw π (withLoc b.L).naut.etaTinv) ((1 - ((withLoc b.L).R.nV : ℝ)) / 2)
      (Formalism.MainNotions.N.mapRep (castQ hpq).symm.toRingHom (Formalism.MainNotions.N.mapRep
        ((Formalism.MainNotions.N.iotaOQ (withLoc b.L).nd (withLoc b.L).naut a).comp ((withLoc b.L).ntw.twist₂ a))
        ((withLoc b.L).ntw.rhoS _ s))) := by
    rw [← hφ0, mapRep_mapRep]
    exact hR
  exact conj_of_isRepOf (withLoc b.L) ((withLoc b.L).naut.iotaQC a) _ _ hcheb _ _
    (isRepOf_cast (withLoc b.L) hpq _ _ _ _ hR') (rhoOfRow_isRepOf (withLoc b.L) hG hC hη a π _ _)

end GlobalTheory.HeightCounting.FitRho

namespace GlobalTheory.HeightCounting

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem nRhoTied_withLoc : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D' : D7) (b : NBuilt hL D'), (∀ x : b.D.LL0, star (x : b.D.what₂.LL) ∈ b.D.LL0) → (∀ j g, ∃ z : ℤ, eExp b.D j g = z) → (∀ v, v ∈ placesOver b.D.host.E b.D.host.pde ∨ v ∈ placesOver b.D.host.E b.D.host.pde' → IsSplitPl b.D.host v) → GlobalTheory.RowTie.ChebSplit b.D.nd → TypesOpen (withLoc b.L) b.jE → NR.NRhoTied (withLoc b.L) := by
  intro hL D' b _ _ _ hcheb hT
  exact ⟨hT.rbarSS, hT.rbar, fun hP hG hC hη a s hs hj =>
    FitRho.rhoS_withLoc hL D' b hcheb hP hG hC hη a s hs hj⟩

end GlobalTheory.HeightCounting
