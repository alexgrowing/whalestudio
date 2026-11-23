import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.KerJoinS
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.I0M
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemFlagUnipotentRadicalIffSecondModel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLeviPreimageOfFixIsotropicFramesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsOrthogonalComplementPreimageOfFixLineStatement
import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.FundamentalContinuity.AdelicIsomorphismStatement
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.SG.AdBridge GlobalTheory.BesselChar

noncomputable section

namespace GlobalTheory.Core.SBesLevi

variable {D : D7}

theorem bridge_fix (D : D7) (g : GA D (D.sp.Y 0)) (x : Fin (Formalism.L2.SG.InstExistsPf.instOf D).n → (Formalism.L2.SG.InstExistsPf.instOf D).E) :
    (mt (D.sp.Y 0) g *ᵥ (fun k => incA D (x k)) = fun k => incA D (x k)) ↔
    ((∀ v, uMat ((Formalism.IndefR.RationalEmbedding.iota D g).1 v) *ᵥ rv (Formalism.L2.SG.InstExistsPf.instOf D) v x = rv (Formalism.L2.SG.InstExistsPf.instOf D) v x) ∧
      (Formalism.L2.SG.InstExistsPf.instOf D).fmat (Formalism.IndefR.RationalEmbedding.iota D g).2 *ᵥ incl (Formalism.L2.SG.InstExistsPf.instOf D) x = incl (Formalism.L2.SG.InstExistsPf.instOf D) x) := by
  have hb := Formalism.IndefR.RationalEmbedding.iota_symm_isBridge D (Formalism.IndefR.RationalEmbedding.iota D g)
  have key : (Formalism.IndefR.RationalEmbedding.iota D).symm (Formalism.IndefR.RationalEmbedding.iota D g) = g :=
    (Formalism.IndefR.RationalEmbedding.iota D).symm_apply_apply g
  have hb1 : ∀ v, uMat ((Formalism.IndefR.RationalEmbedding.iota D g).1 v) = ofHAInf (Formalism.IndefR.RationalEmbedding.inst D) g v :=
    fun v => (hb.1 v).trans (congrArg (fun q => ofHAInf (Formalism.IndefR.RationalEmbedding.inst D) q v) key)
  have hb2 : (Formalism.IndefR.RationalEmbedding.inst D).fmat (Formalism.IndefR.RationalEmbedding.iota D g).2 = ofHAFin (Formalism.IndefR.RationalEmbedding.inst D) g :=
    hb.2.trans (congrArg (fun q => ofHAFin (Formalism.IndefR.RationalEmbedding.inst D) q) key)
  have hdet : ∀ v, IsUnit ((Formalism.L2.SG.InstExistsPf.instOf D).P v).det :=
    fun v => (Matrix.isUnit_iff_isUnit_det _).1 ((Formalism.L2.SG.InstExistsPf.instOf D).P_unit v)
  have hinf : ∀ v, (uMat ((Formalism.IndefR.RationalEmbedding.iota D g).1 v) *ᵥ rv (Formalism.L2.SG.InstExistsPf.instOf D) v x = rv (Formalism.L2.SG.InstExistsPf.instOf D) v x) ↔
      ∀ i, thetaV (Formalism.L2.SG.InstExistsPf.instOf D) v ((hmat (Formalism.L2.SG.InstExistsPf.instOf D) g *ᵥ fun k => incA D (x k)) i) =
        thetaV (Formalism.L2.SG.InstExistsPf.instOf D) v (incA D (x i)) := by
    intro v
    have hθ : (hmat (Formalism.L2.SG.InstExistsPf.instOf D) g).map (thetaV (Formalism.L2.SG.InstExistsPf.instOf D) v) *ᵥ
        (fun i => (Formalism.L2.SG.InstExistsPf.instOf D).φ v (x i)) =
        fun i => thetaV (Formalism.L2.SG.InstExistsPf.instOf D) v ((hmat (Formalism.L2.SG.InstExistsPf.instOf D) g *ᵥ fun k => incA D (x k)) i) := by
      funext i
      refine Eq.trans ?_ (RingHom.map_mulVec (thetaV (Formalism.L2.SG.InstExistsPf.instOf D) v) (hmat (Formalism.L2.SG.InstExistsPf.instOf D) g) (fun k => incA D (x k)) i).symm
      congr 1
      funext k
      exact (GlobalTheory.Core.SBesFlagTie.thetaV_incA v (x k)).symm
    have hφ : (fun i => (Formalism.L2.SG.InstExistsPf.instOf D).φ v (x i)) =
        fun i => thetaV (Formalism.L2.SG.InstExistsPf.instOf D) v (incA D (x i)) :=
      funext fun i => (GlobalTheory.Core.SBesFlagTie.thetaV_incA v (x i)).symm
    rw [hb1 v]
    unfold ofHAInf rv
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hdet v), Matrix.mul_one,
      ← Matrix.mulVec_mulVec, hθ, hφ]
    constructor
    · intro h i
      have := congrArg (fun w => (Formalism.L2.SG.InstExistsPf.instOf D).P v *ᵥ w) h
      simp only [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hdet v), Matrix.one_mulVec] at this
      exact congrFun this i
    · intro h
      rw [funext h]
  have hfin : ((Formalism.L2.SG.InstExistsPf.instOf D).fmat (Formalism.IndefR.RationalEmbedding.iota D g).2 *ᵥ incl (Formalism.L2.SG.InstExistsPf.instOf D) x =
      incl (Formalism.L2.SG.InstExistsPf.instOf D) x) ↔
      ∀ i, tauF (Formalism.L2.SG.InstExistsPf.instOf D) ((hmat (Formalism.L2.SG.InstExistsPf.instOf D) g *ᵥ fun k => incA D (x k)) i) =
        tauF (Formalism.L2.SG.InstExistsPf.instOf D) (incA D (x i)) := by
    have hτ : (hmat (Formalism.L2.SG.InstExistsPf.instOf D) g).map (tauF (Formalism.L2.SG.InstExistsPf.instOf D)) *ᵥ
        incl (Formalism.L2.SG.InstExistsPf.instOf D) x =
        fun i => tauF (Formalism.L2.SG.InstExistsPf.instOf D) ((hmat (Formalism.L2.SG.InstExistsPf.instOf D) g *ᵥ fun k => incA D (x k)) i) := by
      funext i
      refine Eq.trans ?_ (RingHom.map_mulVec (tauF (Formalism.L2.SG.InstExistsPf.instOf D)) (hmat (Formalism.L2.SG.InstExistsPf.instOf D) g) (fun k => incA D (x k)) i).symm
      congr 1
      funext k
      exact (GlobalTheory.Core.SBesFlagTie.tauF_incA (x k)).symm
    have hi : incl (Formalism.L2.SG.InstExistsPf.instOf D) x = fun i => tauF (Formalism.L2.SG.InstExistsPf.instOf D) (incA D (x i)) :=
      funext fun i => (GlobalTheory.Core.SBesFlagTie.tauF_incA (x i)).symm
    have e1 := hb2
    unfold ofHAFin at e1
    change (Formalism.L2.SG.InstExistsPf.instOf D).fmat (Formalism.IndefR.RationalEmbedding.iota D g).2 = _ at e1
    rw [e1, hτ, hi]
    exact funext_iff
  rw [hfin, forall_congr' hinf]
  change ((hmat (Formalism.L2.SG.InstExistsPf.instOf D) g *ᵥ fun k => incA D (x k)) = fun k => incA D (x k)) ↔ _
  constructor
  · intro h
    exact ⟨fun v i => by rw [congrFun h i], fun i => by rw [congrFun h i]⟩
  · rintro ⟨h1, h2⟩
    funext i
    have := Formalism.L2.SG.Pf.TT_ext (Formalism.L2.SG.InstExistsPf.instOf D)
      ((hmat (Formalism.L2.SG.InstExistsPf.instOf D) g *ᵥ fun k => incA D (x k)) i - (show AF (Formalism.L2.SG.InstExistsPf.instOf D).F ⊗[(Formalism.L2.SG.InstExistsPf.instOf D).F] (Formalism.L2.SG.InstExistsPf.instOf D).E from incA D (x i)))
      (fun v => by rw [map_sub, h1 v i, sub_self]) (by rw [map_sub, h2 i, sub_self])
    exact sub_eq_zero.1 this

theorem transport_fix (D : D7) (I : AutInst) (ιE : I.E ≃+* D.host.E) (hId : ∀ y, HEq (ιE y) y)
    (hI : I = Formalism.L2.SG.InstExistsPf.instOf D) (hr : (D.sp.Y 0).rank = I.n) (S : Set (Fin I.n → I.E))
    (s : (Formalism.L2.SG.InstExistsPf.instOf D).GA) :
    ((castGA hI.symm s).1 ∈ Formalism.L2.SG.PoincareInHH.HinfS I S ∧ (castGA hI.symm s).2 ∈ Formalism.L2.SG.PoincareInHH.HfinS I S) ↔
    ∀ p ∈ S, (∀ v, uMat (s.1 v) *ᵥ rv (Formalism.L2.SG.InstExistsPf.instOf D) v (fun k => ιE (p (Fin.cast hr k))) =
        rv (Formalism.L2.SG.InstExistsPf.instOf D) v (fun k => ιE (p (Fin.cast hr k)))) ∧
      (Formalism.L2.SG.InstExistsPf.instOf D).fmat s.2 *ᵥ incl (Formalism.L2.SG.InstExistsPf.instOf D) (fun k => ιE (p (Fin.cast hr k))) =
        incl (Formalism.L2.SG.InstExistsPf.instOf D) (fun k => ιE (p (Fin.cast hr k))) := by
  generalize hI.symm = e
  subst hI
  have hid : ∀ y, ιE y = y := fun y => eq_of_heq (hId y)
  have hv : ∀ p : Fin (Formalism.L2.SG.InstExistsPf.instOf D).n → (Formalism.L2.SG.InstExistsPf.instOf D).E,
      (fun k : Fin (Formalism.L2.SG.InstExistsPf.instOf D).n => ιE (p (Fin.cast hr k))) = p := fun p => funext fun k => by rw [hid]; rfl
  rw [GlobalTheory.Core.SBesFlagTie.castGA_self]
  change ((∀ v, ∀ x ∈ S, uMat (s.1 v) *ᵥ rv _ v x = rv _ v x) ∧ (∀ y ∈ S, _)) ↔ _
  constructor
  · rintro ⟨h1, h2⟩ p hp
    rw [hv p]
    exact ⟨fun v => h1 v p hp, h2 p hp⟩
  · intro H
    refine ⟨fun v p hp => ?_, fun p hp => ?_⟩
    · have := (H p hp).1 v
      rw [hv p] at this
      exact this
    · have := (H p hp).2
      rw [hv p] at this
      exact this

theorem fix_smul {S : HSp D} (g : GA D S) {c : D.host.E} (hc : c ≠ 0) (y : Fin S.rank → D.host.E) :
    (mt S g *ᵥ (fun k => incA D ((c • y) k)) = fun k => incA D ((c • y) k)) ↔
      (mt S g *ᵥ (fun k => incA D (y k)) = fun k => incA D (y k)) := by
  have hs : (fun k => incA D ((c • y) k)) = incA D c • fun k => incA D (y k) := by
    funext k
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  have hu : IsUnit (incA D c) := (IsUnit.mk0 c hc).map (incA D)
  rw [hs, Matrix.mulVec_smul]
  exact hu.smul_left_cancel

theorem fix_cols {S : HSp D} (g : GA D S) {ρ : ℕ} (e : Matrix (Fin S.rank) (Fin ρ) D.host.E) :
    mt S g ⬝ rat e = rat e ↔ ∀ a, (mt S g *ᵥ (fun k => incA D (e k a)) = fun k => incA D (e k a)) := by
  constructor
  · intro h a
    funext k
    exact congrFun (congrFun h k) a
  · intro h
    funext k a
    exact congrFun (h a) k

theorem rat_mulVec {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) (w : Fin n → D.host.E) :
    (fun k => incA D ((M *ᵥ w) k)) = rat M *ᵥ fun k => incA D (w k) := by
  funext k
  exact RingHom.map_mulVec (incA D) M w k

theorem range_embA_iff {S V₀ A L : HSp D} {ρ : ℕ} (d : HypDec S V₀ ρ) (o : OrthDec V₀ A L) (ζ : Fin L.rank → D.host.E)
    (hζ : IsLineVec L ζ) (g : GA D S) :
    g ∈ (embA d o).range ↔ (mt S g ⬝ d.jX = d.jX ∧ mt S g ⬝ d.jY = d.jY ∧
      (mt S g *ᵥ (fun k => incA D ((d.i₀ *ᵥ vecB o ζ) k)) = fun k => incA D ((d.i₀ *ᵥ vecB o ζ) k))) := by
  have hw : (fun k => incA D (vecB o ζ k)) = o.jB *ᵥ fun k => incA D (ζ k) := rat_mulVec o.iB ζ
  rw [rat_mulVec d.i₀ (vecB o ζ)]
  change _ ↔ (_ ∧ _ ∧ mt S g *ᵥ (d.j0 *ᵥ _) = d.j0 *ᵥ _)
  constructor
  · rintro ⟨a, rfl⟩
    change mt S (d.emb0 (o.emb (a, 1))) ⬝ d.jX = d.jX ∧ mt S (d.emb0 (o.emb (a, 1))) ⬝ d.jY = d.jY ∧
      mt S (d.emb0 (o.emb (a, 1))) *ᵥ (d.j0 *ᵥ _) = d.j0 *ᵥ _
    refine ⟨d.wittDecomp_anisotropicEmbedding_inclX _, d.wittDecomp_anisotropicEmbedding_inclY _, ?_⟩
    rw [Matrix.mulVec_mulVec, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_mulVec (M := mt V₀ _), o.emb_jB,
      MixModel.mt_one, Matrix.mul_one]
  · rintro ⟨h1, h2, h3⟩
    obtain ⟨b, rfl⟩ := GlobalTheory.T.exists_levi_preimage_of_fix_isotropic_frames d g h1 h2
    have hb : (mt V₀ b *ᵥ fun k => incA D (vecB o ζ k)) = fun k => incA D (vecB o ζ k) := by
      rw [Matrix.mulVec_mulVec, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, ← Matrix.mulVec_mulVec] at h3
      have := congrArg (fun w => d.p0 *ᵥ w) h3
      simp only [Matrix.mulVec_mulVec, d.p0_j0, Matrix.one_mulVec] at this
      simpa only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, d.p0_j0, Matrix.one_mul] using this
    obtain ⟨a, ha⟩ := GlobalTheory.T.exists_orthogonalComplement_preimage_of_fix_line o ζ hζ b hb
    exact ⟨a, by rw [← ha]; rfl⟩

theorem range_embA_eq_H : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (t lam : D.host.E), t ≠ 0 → lam ≠ 0 → IdE X → ∀ (V₀ L : HSp D) (d : HypDec (D.sp.Y 0) V₀ D.R.rS) (o : OrthDec V₀ (D.sp.X 0) L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → d.e = GlobalTheory.Core.SBesEx.eM X h t lam → d.e' = GlobalTheory.Core.SBesEx.e'M X h t lam → d.i₀ *ᵥ vecB o ζ = t • GlobalTheory.Core.SBesEx.cY X h (X.zu u) → ∀ g, g ∈ (embA d o).range ↔ (iotaX X h g).1 ∈ Hinf X u ∧ (iotaX X h g).2 ∈ Hfin X u := by
  intro D X h u t lam ht hl hId V₀ L d o ζ hζ he he' hz g
  have hsc : ∀ a, GlobalTheory.Core.SBesEx.scl t lam a ≠ 0 := fun a => mul_ne_zero ht (pow_ne_zero _ hl)
  have hR : ((iotaX X h g).1 ∈ Hinf X u ∧ (iotaX X h g).2 ∈ Hfin X u) ↔
      ∀ p ∈ fixSet X u, (mt (D.sp.Y 0) g *ᵥ (fun k => incA D (X.ιE (p (Fin.cast (rank_eq X h) k)))) =
        fun k => incA D (X.ιE (p (Fin.cast (rank_eq X h) k)))) :=
    (transport_fix D X.B.I X.ιE hId h (rank_eq X h) (fixSet X u) (Formalism.IndefR.RationalEmbedding.iota D g)).trans
      (forall₂_congr fun p _ => (bridge_fix D g _).symm)
  rw [range_embA_iff d o ζ hζ g, hR, HypDec.jX, HypDec.jY, fix_cols, fix_cols]
  change _ ↔ ∀ p ∈ Set.range X.eR ∪ Set.range X.fR ∪ {X.zR u}, _
  have hE : ∀ a, (fun k => d.e k a) = GlobalTheory.Core.SBesEx.scl t lam a • GlobalTheory.Core.SBesEx.cY X h (X.eX a) := by
    intro a; funext k; rw [he]; rfl
  have hE' : ∀ a, (fun k => d.e' k a) = (star (GlobalTheory.Core.SBesEx.scl t lam a))⁻¹ • GlobalTheory.Core.SBesEx.cY X h (X.fY a) := by
    intro a; funext k; rw [he']; rfl
  have hA : ∀ a, ((mt (D.sp.Y 0) g *ᵥ fun k => incA D (d.e k a)) = fun k => incA D (d.e k a)) ↔
      ((mt (D.sp.Y 0) g *ᵥ fun k => incA D (X.ιE (X.eR a (Fin.cast (rank_eq X h) k)))) =
        fun k => incA D (X.ιE (X.eR a (Fin.cast (rank_eq X h) k)))) := fun a => by
    have := fix_smul g (hsc a) (GlobalTheory.Core.SBesEx.cY X h (X.eX a))
    rw [← hE a] at this
    exact this
  have hB : ∀ a, ((mt (D.sp.Y 0) g *ᵥ fun k => incA D (d.e' k a)) = fun k => incA D (d.e' k a)) ↔
      ((mt (D.sp.Y 0) g *ᵥ fun k => incA D (X.ιE (X.fR a (Fin.cast (rank_eq X h) k)))) =
        fun k => incA D (X.ιE (X.fR a (Fin.cast (rank_eq X h) k)))) := fun a => by
    have := fix_smul g (inv_ne_zero (star_ne_zero.2 (hsc a))) (GlobalTheory.Core.SBesEx.cY X h (X.fY a))
    rw [← hE' a] at this
    exact this
  have hC : ((mt (D.sp.Y 0) g *ᵥ fun k => incA D ((d.i₀ *ᵥ vecB o ζ) k)) = fun k => incA D ((d.i₀ *ᵥ vecB o ζ) k)) ↔
      ((mt (D.sp.Y 0) g *ᵥ fun k => incA D (X.ιE (X.zR u (Fin.cast (rank_eq X h) k)))) =
        fun k => incA D (X.ιE (X.zR u (Fin.cast (rank_eq X h) k)))) := by
    have := fix_smul g ht (GlobalTheory.Core.SBesEx.cY X h (X.zu u))
    rw [← hz] at this
    exact this
  simp only [hA, hB, hC]
  constructor
  · rintro ⟨h1, h2, h3⟩ p hp
    rcases hp with (⟨a, rfl⟩ | ⟨a, rfl⟩) | hp
    · exact h1 a
    · exact h2 a
    · rw [Set.mem_singleton_iff] at hp
      subst hp
      exact h3
  · intro H
    exact ⟨fun a => H _ (Or.inl (Or.inl ⟨a, rfl⟩)), fun a => H _ (Or.inl (Or.inr ⟨a, rfl⟩)), H _ (Or.inr rfl)⟩

end GlobalTheory.Core.SBesLevi

end
