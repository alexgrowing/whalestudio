import Formalism.AdmissibleDesigns.MultVZeroOfSubsingleton
import Formalism.AdmissibleDesigns.LocCont
import Formalism.AdmissibleDesigns.MsContW

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

set_option synthInstance.maxHeartbeats 400000

open Classical

namespace Formalism.MainNotions.N.K.Font

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.KHf Formalism.MainNotions.N.KDim NumberField IsDedekindDomain Formalism.NG Formalism.BasicNotions

section Loc

variable {D : D7} (i : D.nd.Loc) {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i))

theorem loc_apply {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (g : Br.G D.nbr i w hw) (a b : Fin k) :
    Br.loc D.nbr i w hw M g a b =
      eK (D.nbr i w hw) (toK D.nd i (M ((Br.iota D.nbr i w hw g : _) : GE D.nd) a b)) := by
  exact (Br.toLLK_alg (Bw := D.nbr i w hw) (c := M ((Br.iota D.nbr i w hw g : _) : GE D.nd) a b)).symm

theorem locChi_apply (χ : GE D.nd →* (D.nd.O i)ˣ) (g : Br.G D.nbr i w hw) :
    ((Br.locChi D.nbr i w hw χ g : (Br.LL D.nbr i w hw)ˣ) : Br.LL D.nbr i w hw) =
      eK (D.nbr i w hw) (toK D.nd i ((χ ((Br.iota D.nbr i w hw g : _) : GE D.nd) : (D.nd.O i)ˣ) : D.nd.O i)) := by
  exact (IsFractionRing.lift_algebraMap (Br.toLL_inj (D.nbr i w hw))
    ((χ ((Br.iota D.nbr i w hw g : _) : GE D.nd) : (D.nd.O i)ˣ) : D.nd.O i)).symm

end Loc

section Ident

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (g0 : GE D.nd)
  (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))

abbrev MrTw {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) (x : D.nd.X i) :
    Br.G D.nbr i w hw →* Matrix (Fin D.R.nV) (Fin D.R.nV) (Br.LL D.nbr i w hw) :=
  twistM (TruncatedSeriesCountingIdentities.locC (TruncatedSeriesCountingIdentities.CoefExt.self i w hw) (rO D.nd i r x)) (TruncatedSeriesCountingIdentities.chi1C (TruncatedSeriesCountingIdentities.CoefExt.self i w hw))⁻¹

theorem repX_mulVec (x' : Dd.X') (n : ℕ) (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i))
    (g : Br.G D.nbr i _ hn) (v : TrV (eK (D.nbr i _ hn)) (EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x')) :
    ((KDim.repX i dc Dd.r Dd.χ x' n hn g v : EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x') : Fin D.R.nV → FractionRing (D.nd.O i)) =
      (((Formalism.NG.uElt Dd.r Dd.χ ((Br.iota D.nbr i _ hn g : _) : GE D.nd) : Dd.R') : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) x').mulVec
        (v : Fin D.R.nV → FractionRing (D.nd.O i)) := by
  rfl

abbrev phiL (x' : Dd.X') {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) :
    TrV (eK (D.nbr i w hw)) (EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x') ≃ₗ[Br.LL D.nbr i w hw] (Fin D.R.nV → Br.LL D.nbr i w hw) :=
  phiX i Dd x' (eK (D.nbr i w hw))

theorem phiX_equiv (hD : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0
      eB e₁ s Dd)
    (x' : Dd.X') (n : ℕ) (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i))
    (g : Br.G D.nbr i _ hn) (v : TrV (eK (D.nbr i _ hn)) (EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x')) :
    phiL i Dd x' hn (KDim.repX i dc Dd.r Dd.χ x' n hn g v) =
      matRep (MrTw i r hn (Dd.p x')) g (phiL i Dd x' hn v) := by
  obtain ⟨-, -, -, -, -, -, hr, -, hsm, -, -, hχ, -⟩ := hD
  funext j
  have hv := congrArg (eK (D.nbr i _ hn)) (congrFun (repX_mulVec i dc Dd x' n hn g v) j)
  refine hv.trans ?_
  change _ = ((MrTw i r hn (Dd.p x')) g).mulVec
    (fun k => eK (D.nbr i _ hn) ((v : Fin D.R.nV → FractionRing (D.nd.O i)) k)) j
  have hu : ∀ h : GE D.nd, ((((Dd.χ h)⁻¹ : (Dd.T')ˣ) : Dd.T') : Dd.X' → D.nd.O i) x' =
      (((chiU D.nd i 1 h)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) := by
    intro h
    rw [← map_inv, hχ, map_inv]
  have hrep : ∀ (h : GE D.nd) (y : D.nd.X i), RepresentationBoundsCohomology.repX D.nd r h y = rO D.nd i r y h := fun _ _ => rfl
  simp [Formalism.NG.uElt, hsm, hr, hu, hrep, MrTw, twistM, TruncatedSeriesCountingIdentities.locC, TruncatedSeriesCountingIdentities.chi1C, mapM, loc_apply, locChi_apply,
    Matrix.mulVec, dotProduct, Matrix.smul_apply, Matrix.map_apply, map_sum, map_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  refine congrArg₂ (· * ·) (congrArg₂ (· * ·) ?_ ?_) ?_
  · exact ((Units.val_inv_eq_inv_val
      (TruncatedSeriesCountingIdentities.chi1C (TruncatedSeriesCountingIdentities.CoefExt.self i _ hn) g : (Br.LL D.nbr i _ hn)ˣ)).trans
      (congrArg Inv.inv (locChi_apply i hn (chiU D.nd i 1) g))).symm
  · exact (loc_apply i hn (rO D.nd i r (Dd.p x')) g j k).symm
  · rfl

theorem crysX_of (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (hG2 : TruncatedSeriesCountingIdentities.admG2 i r ρ π)
    (hD : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0
      eB e₁ s Dd) (x' : Dd.X') (l : K.Col i dc) :
    KDim.CrysX i dc Dd.r Dd.χ x' l := by
  have hn := col_over i dc l
  have hc := (hG2 _ hn (TruncatedSeriesCountingIdentities.CoefExt.self i _ hn)).2 (Dd.p x')
  unfold KDim.CrysX
  exact crys_of_mat _ _ _ (phiL i Dd x' hn) (phiX_equiv i dc r π g0 eB e₁ s Dd hD x' _ hn) hc

end Ident

section BC

theorem smulMV {Kf : Type} [CommRing Kf] {n m : ℕ} (c : Kf) (M : Matrix (Fin n) (Fin m) Kf) (u : Fin m → Kf) :
    (c • M).mulVec u = c • M.mulVec u := by
  ext a
  simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply, Finset.mul_sum, mul_assoc]

variable {Kf LL : Type} [Field Kf] [Field LL] (f : Kf ≃+* LL) {n r t : ℕ}
  (e : (Fin n → Kf) ≃ₗ[Kf] (Fin r → Kf) × (Fin t → Kf))

def eL : (Fin n → LL) ≃ₗ[LL] (Fin r → LL) × (Fin t → Fin 1 → LL) where
  toFun v := (fun a => f ((e (fun b => f.symm (v b))).1 a), fun j _ => f ((e (fun b => f.symm (v b))).2 j))
  invFun z := fun b => f (e.symm (fun a => f.symm (z.1 a), fun j => f.symm (z.2 j 0)) b)
  map_add' u v := by
    have h : (fun b => f.symm ((u + v) b)) = (fun b => f.symm (u b)) + (fun b => f.symm (v b)) :=
      funext fun b => by simp
    refine Prod.ext (funext fun a => ?_) (funext fun j => funext fun x => ?_)
    · show f ((e (fun b => f.symm ((u + v) b))).1 a) =
        f ((e (fun b => f.symm (u b))).1 a) + f ((e (fun b => f.symm (v b))).1 a)
      rw [h, map_add, Prod.fst_add, Pi.add_apply, map_add]
    · show f ((e (fun b => f.symm ((u + v) b))).2 j) =
        f ((e (fun b => f.symm (u b))).2 j) + f ((e (fun b => f.symm (v b))).2 j)
      rw [h, map_add, Prod.snd_add, Pi.add_apply, map_add]
  map_smul' c v := by
    have h : (fun b => f.symm ((c • v) b)) = f.symm c • (fun b => f.symm (v b)) :=
      funext fun b => by simp
    refine Prod.ext (funext fun a => ?_) (funext fun j => funext fun x => ?_)
    · show f ((e (fun b => f.symm ((c • v) b))).1 a) = c * f ((e (fun b => f.symm (v b))).1 a)
      rw [h, map_smul, Prod.smul_fst, Pi.smul_apply, smul_eq_mul, map_mul, RingEquiv.apply_symm_apply]
    · show f ((e (fun b => f.symm ((c • v) b))).2 j) = c * f ((e (fun b => f.symm (v b))).2 j)
      rw [h, map_smul, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, map_mul, RingEquiv.apply_symm_apply]
  left_inv v := by
    funext b
    simp
  right_inv z := by
    refine Prod.ext (funext fun a => ?_) (funext fun j => funext fun x => ?_)
    · simp
    · rw [Fin.fin_one_eq_zero x]
      simp

theorem eL_apply (v : Fin n → LL) :
    eL f e v = (fun a => f ((e (fun b => f.symm (v b))).1 a), fun j _ => f ((e (fun b => f.symm (v b))).2 j)) := rfl

theorem eL_mul (R : Matrix (Fin n) (Fin n) Kf) (P : Matrix (Fin r) (Fin r) Kf) (c : Fin t → Kf)
    (he : ∀ u, e (R.mulVec u) = (P.mulVec (e u).1, fun j => c j * (e u).2 j))
    (R' : Matrix (Fin n) (Fin n) LL) (P' : Matrix (Fin r) (Fin r) LL) (c' : Fin t → LL)
    (hR : ∀ a b, R' a b = f (R a b)) (hP : ∀ a b, P' a b = f (P a b)) (hc : ∀ j, c' j = f (c j))
    (v : Fin n → LL) :
    eL f e (R'.mulVec v) = (P'.mulVec (eL f e v).1, fun j _ => c' j * (eL f e v).2 j 0) := by

  have key : (fun b => f.symm ((R'.mulVec v) b)) = R.mulVec (fun b => f.symm (v b)) := by
    funext b
    simp only [Matrix.mulVec, dotProduct, hR, map_sum, map_mul, RingEquiv.symm_apply_apply]
  have h2 : e (fun b => f.symm ((R'.mulVec v) b)) =
      (P.mulVec (e (fun b => f.symm (v b))).1, fun j => c j * (e (fun b => f.symm (v b))).2 j) :=
    (congrArg e key).trans (he _)
  rw [eL_apply, eL_apply, h2]
  refine Prod.ext (funext fun a => ?_) (funext fun j => funext fun x => ?_)
  · simp only [Matrix.mulVec, dotProduct, hP, map_sum, map_mul]
  · simp only [hc, map_mul]

end BC

section Dec

variable {D : D7} (i : D.nd.Loc)
  (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

theorem chiRat_cont (c : ℕ) : Continuous (chiRatO D.nd i c) := by
  have e : (fun g : GE D.nd => (((chiU D.nd i c * (chiU D.nd i 1)⁻¹) g : (D.nd.O i)ˣ) : D.nd.O i)) =
      fun g => ((chiU D.nd i c g : (D.nd.O i)ˣ) : D.nd.O i) * ((chiU D.nd i 1 g⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) := by
    funext g
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, map_inv, Units.val_mul]
  have hχ : Continuous fun g : GE D.nd => (((chiU D.nd i c * (chiU D.nd i 1)⁻¹) g : (D.nd.O i)ˣ) : D.nd.O i) := by
    rw [e]
    exact (D.nd.chi_cont i c).mul ((D.nd.chi_cont i 1).comp continuous_inv)
  show Continuous fun g => (((chiU D.nd i c * (chiU D.nd i 1)⁻¹) g : (D.nd.O i)ˣ) : D.nd.O i) •
    ((1 : GE D.nd →* Matrix (Fin 1) (Fin 1) (D.nd.O i)) g)
  exact hχ.smul (continuous_const : Continuous fun _ : GE D.nd => (1 : Matrix (Fin 1) (Fin 1) (D.nd.O i)))

theorem locC_cont' {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hM : Continuous M)
    {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) :
    Continuous ⇑(TruncatedSeriesCountingIdentities.locC C M) := by
  have hinc : Continuous (TruncatedSeriesCountingIdentities.CoefExt.inc C) :=
    continuous_induced_rng.2 (by exact continuous_subtype_val)
  exact (KOrb.loc_cont i hw M hM).matrix_map hinc

abbrev MsC {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) (j : Fin D.R.t) :
    Br.G D.nbr i w hw →* Matrix (Fin 1) (Fin 1) (Br.LL D.nbr i w hw) :=
  TruncatedSeriesCountingIdentities.locC (TruncatedSeriesCountingIdentities.CoefExt.self i w hw) (chiRatO D.nd i ((j : ℕ) + 1))

theorem mrTw_eq {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) (x : D.nd.X i) :
    twistM (TruncatedSeriesCountingIdentities.locC (TruncatedSeriesCountingIdentities.CoefExt.self i w hw) (rO D.nd i r x)) (TruncatedSeriesCountingIdentities.chi1C (TruncatedSeriesCountingIdentities.CoefExt.self i w hw))⁻¹ =
      TBa.MsW i r hw x := by
  ext g a b
  simp [TBa.MsW, TruncatedSeriesCountingIdentities.locC, TruncatedSeriesCountingIdentities.chi1C, rTwO, mapM, twistM, loc_apply, locChi_apply]

end Dec

section DecRec

variable {D : D7} (i : D.nd.Loc)
  (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

theorem decomp_at (hDec : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) {w : HeightOneSpectrum (𝓞 D.host.E)}
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) :
    ∃ e' : (Fin D.R.nV → Br.LL D.nbr i w hw) ≃ₗ[Br.LL D.nbr i w hw]
        (Fin D.R.r → Br.LL D.nbr i w hw) × (Fin D.R.t → Fin 1 → Br.LL D.nbr i w hw),
      ∀ g v, e' (matRep (Kf := Br.LL D.nbr i w hw) (TBa.MsW i r hw π) g v) =
        (matRep (Br.loc D.nbr i w hw (WpO D.nd i ρ π)) g (e' v).1, TBa.sumRep (MsC i hw) id g (e' v).2) := by
  obtain ⟨e, he⟩ := hDec
  refine ⟨eL (eK (D.nbr i w hw)) e, fun g v => ?_⟩
  obtain ⟨h, hh⟩ : ∃ h : GE D.nd, h = ((Br.iota D.nbr i w hw g : _) : GE D.nd) := ⟨_, rfl⟩

  have hE : ∀ u, e ((toK D.nd i (((chiU D.nd i 1 h)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) • mapM (toK D.nd i) (rO D.nd i r π) h).mulVec u) =
      ((toK D.nd i (((chiU D.nd i 1 h)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) • mapM (toK D.nd i) (rhoO D.nd i ρ π) h).mulVec (e u).1,
        fun j : Fin D.R.t => toK D.nd i ((chiU D.nd i ((j : ℕ) + 1) h : (D.nd.O i)ˣ) : D.nd.O i) * toK D.nd i (((chiU D.nd i 1 h)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) * (e u).2 j) := by
    intro u
    rw [smulMV, smulMV, map_smul, he h u]
    refine Prod.ext rfl (funext fun j => ?_)
    simp only [Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
    ring
  have hR : ∀ a b, TBa.MsW i r hw π g a b =
      eK (D.nbr i w hw) ((toK D.nd i (((chiU D.nd i 1 h)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) • mapM (toK D.nd i) (rO D.nd i r π) h) a b) := by
    intro a b
    subst hh
    simp [TBa.MsW, TruncatedSeriesCountingIdentities.locC, rTwO, twistM, mapM, loc_apply] <;> rfl
  have hP : ∀ a b, Br.loc D.nbr i w hw (WpO D.nd i ρ π) g a b =
      eK (D.nbr i w hw) ((toK D.nd i (((chiU D.nd i 1 h)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) • mapM (toK D.nd i) (rhoO D.nd i ρ π) h) a b) := by
    intro a b
    subst hh
    simp [WpO, twistM, mapM, loc_apply] <;> rfl
  have hc : ∀ j : Fin D.R.t, MsC i hw j g 0 0 = eK (D.nbr i w hw) (toK D.nd i ((chiU D.nd i ((j : ℕ) + 1) h : (D.nd.O i)ˣ) : D.nd.O i) * toK D.nd i (((chiU D.nd i 1 h)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i)) := by
    intro j
    subst hh
    refine (loc_apply i hw (chiRatO D.nd i ((j : ℕ) + 1)) g 0 0).trans ?_
    congr 1
    simp [chiRatO, twistM]
  have key := eL_mul (eK (D.nbr i w hw)) e
    (toK D.nd i (((chiU D.nd i 1 h)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) • mapM (toK D.nd i) (rO D.nd i r π) h)
    (toK D.nd i (((chiU D.nd i 1 h)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) • mapM (toK D.nd i) (rhoO D.nd i ρ π) h)
    (fun j : Fin D.R.t => toK D.nd i ((chiU D.nd i ((j : ℕ) + 1) h : (D.nd.O i)ˣ) : D.nd.O i) * toK D.nd i (((chiU D.nd i 1 h)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i))
    hE (TBa.MsW i r hw π g) (Br.loc D.nbr i w hw (WpO D.nd i ρ π) g) (fun j => MsC i hw j g 0 0)
    hR hP hc v
  refine key.trans ?_
  refine Prod.ext rfl (funext fun j => funext fun x => ?_)
  rw [Fin.fin_one_eq_zero x]
  simp [TBa.sumRep, Matrix.mulVec, dotProduct]

theorem wp_font (hF : TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL i) (hG2 : TruncatedSeriesCountingIdentities.admG2 i r ρ π) (hDec : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π)
    (hCont : TruncatedSeriesCountingIdentities.FamilyContinuous i r) (hρ : Continuous fun g => rhoO D.nd i ρ π g)
    {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) :
    IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (Br.loc D.nbr i w hw (WpO D.nd i ρ π))) ∧
      ∀ (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw) (a : ℤ), a < 0 →
        multV (Br.PD D.loc D.nbr i w hw) (matRep (Kf := Br.LL D.nbr i w hw) (TBa.MsW i r hw π)) τ a =
          multV (Br.PD D.loc D.nbr i w hw) (matRep (Br.loc D.nbr i w hw (WpO D.nd i ρ π))) τ a := by
  obtain ⟨e', he'⟩ := decomp_at i r ρ π hDec hw
  have hMsc : ∀ j, Continuous (MsC i hw j) := fun j => locC_cont' i _ (chiRat_cont i _) hw _
  have hWc : Continuous ⇑(Br.loc D.nbr i w hw (WpO D.nd i ρ π)) :=
    KOrb.loc_cont i hw _ (KOrb.wpO_cont i ρ π hρ)
  have hc0 := (hG2 _ hw (TruncatedSeriesCountingIdentities.CoefExt.self i w hw)).2 π
  rw [mrTw_eq] at hc0
  have hc : IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (Kf := Br.LL D.nbr i w hw) (TBa.MsW i r hw π)) := hc0
  have hJ : ∀ (j : Fin D.R.t) (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw) (b : ℤ),
      IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (MsC i hw (id j))) τ b → 0 ≤ b := by
    intro j τ b hb
    have hj := j.2
    have h := ((hG2 _ hw (TruncatedSeriesCountingIdentities.CoefExt.self i w hw)).1.2.2.2.1 ((j : ℕ) + 1) (by omega) (by omega) τ b).1 hb
    rw [h]
    push_cast
    omega
  exact decomp_neg (O := Br.OLL D.nbr i w hw) (Br.PD D.loc D.nbr i w hw) (MsC i hw) (by exact hF _ hw (TruncatedSeriesCountingIdentities.CoefExt.self i w hw)) hMsc
    (TBa.matG (TBa.MsW i r hw) (KOrb.msContW i r hCont hw) π)
    (TBa.matG (fun _ : Unit => Br.loc D.nbr i w hw (WpO D.nd i ρ π)) (fun _ => hWc) ()) id e' he' hc hJ

theorem dR_of_wp (hF : TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL i) (hG2 : TruncatedSeriesCountingIdentities.admG2 i r ρ π) (hDec : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π)
    (hCont : TruncatedSeriesCountingIdentities.FamilyContinuous i r) (hρ : Continuous fun g => rhoO D.nd i ρ π g)
    {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i))
    {V : Type} [AddCommGroup V] [Module (Br.LL D.nbr i w hw) V] [Module ℚ_[D.nd.l i] V]
    [IsScalarTower ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) V]
    (ρ' : Representation (Br.LL D.nbr i w hw) (Br.G D.nbr i w hw) V)
    (e : V ≃ₗ[Br.LL D.nbr i w hw] (Fin D.R.r → Br.LL D.nbr i w hw))
    (he : ∀ g x, e (ρ' g x) = matRep (Br.loc D.nbr i w hw (WpO D.nd i ρ π)) g (e x)) :
    IsDR (Br.PD D.loc D.nbr i w hw) ρ' := by
  have hWc : Continuous ⇑(Br.loc D.nbr i w hw (WpO D.nd i ρ π)) :=
    KOrb.loc_cont i hw _ (KOrb.wpO_cont i ρ π hρ)
  have hcr := (wp_font i r ρ π hF hG2 hDec hCont hρ hw).1
  have hdr := (hF _ hw (TruncatedSeriesCountingIdentities.CoefExt.self i w hw)).2.2.2
    (TBa.matG (fun _ : Unit => Br.loc D.nbr i w hw (WpO D.nd i ρ π)) (fun _ => hWc) ()) hcr
  exact dR_of_mat _ _ _ e he hdr

end DecRec

section Targets

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (g0 : GE D.nd)
  (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))

theorem crysW_of (hF : TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL i) (hG2 : TruncatedSeriesCountingIdentities.admG2 i r ρ π) (hDec : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π)
    (hCont : TruncatedSeriesCountingIdentities.FamilyContinuous i r) (hρ : Continuous fun g => rhoO D.nd i ρ π g) (l : K.Col i dc) :
    KDim.CrysW i dc ρ π l := (wp_font i r ρ π hF hG2 hDec hCont hρ (col_over i dc l)).1

theorem negX_of (hF : TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL i) (hG2 : TruncatedSeriesCountingIdentities.admG2 i r ρ π) (hDec : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π)
    (hCont : TruncatedSeriesCountingIdentities.FamilyContinuous i r) (hρ : Continuous fun g => rhoO D.nd i ρ π g)
    (hD : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0
      eB e₁ s Dd) (x' : Dd.X') (l : K.Col i dc) :
    KDim.NegX i dc Dd.r Dd.χ ρ π x' l := by
  intro τ a ha
  have h1 := multV_mat (Br.PD D.loc D.nbr i _ (col_over i dc l)) (MrTw i r (col_over i dc l) (Dd.p x')) _
    (phiL i Dd x' (col_over i dc l)) (phiX_equiv i dc r π g0 eB e₁ s Dd hD x' _ (col_over i dc l)) τ a
  have h2 := (hG2 _ (col_over i dc l) (TruncatedSeriesCountingIdentities.CoefExt.self i _ (col_over i dc l))).1.2.1 τ (Dd.p x') π a
  have h3 := (wp_font i r ρ π hF hG2 hDec hCont hρ (col_over i dc l)).2 τ a ha
  rw [← mrTw_eq] at h3
  exact h1.trans (h2.trans h3)

end Targets

section RowDR

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

def WpIso (n : ℕ) (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) {V : Type} [AddCommGroup V]
    [Module (FractionRing (D.nd.O i)) V] [Module (D.nd.O i) V] [IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) V]
    (ρT : Representation (D.nd.O i) ↥(Γn i dc n) V) : Prop :=
  ∃ e : TrV (eK (D.nbr i _ hn)) V ≃ₗ[Br.LL D.nbr i _ hn] (Fin D.R.r → Br.LL D.nbr i _ hn),
    ∀ g x, e (repL (eK (D.nbr i _ hn)) ρT (Br.iota D.nbr i _ hn) g x) =
      matRep (Br.loc D.nbr i _ hn (WpO D.nd i ρ π)) g (e x)

theorem isDR_of_wpIso (hF : TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL i) (hG2 : TruncatedSeriesCountingIdentities.admG2 i r ρ π) (hDec : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π)
    (hCont : TruncatedSeriesCountingIdentities.FamilyContinuous i r) (hρ : Continuous fun g => rhoO D.nd i ρ π g)
    (n : ℕ) (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) {V : Type} [AddCommGroup V]
    [Module (FractionRing (D.nd.O i)) V] [Module (D.nd.O i) V] [IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) V]
    (ρT : Representation (D.nd.O i) ↥(Γn i dc n) V) (h : WpIso i dc ρ π n hn ρT) :
    IsDR (Br.PD D.loc D.nbr i _ hn) (repL (eK (D.nbr i _ hn)) ρT (Br.iota D.nbr i _ hn)) := by
  obtain ⟨e, he⟩ := h
  exact dR_of_wp i r ρ π hF hG2 hDec hCont hρ hn _ e he

end RowDR

end Formalism.MainNotions.N.K.Font

end
