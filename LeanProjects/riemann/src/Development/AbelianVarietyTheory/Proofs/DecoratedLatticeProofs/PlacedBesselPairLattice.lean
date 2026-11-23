import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Placed
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartMemFrameStabilizerIffLocalStabilizer
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacedP
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeFrameChain
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSBesUnscaledDual
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntOfSmul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqOfPsiE

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1600000

namespace GlobalTheory.LineIdeal

section Loc

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.FinPlLoc NumberField GlobalTheory.AdelicU
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem int_of_loc {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (y : Af F ⊗[F] E)
    (h : ∀ w, Algebra.TensorProduct.map (evalV F w) (AlgHom.id F E) y ∈ intLoc F E w) :
    y ∈ AddSubgroup.closure {y : Af F ⊗[F] E | ∃ a ∈ intAf F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)} := by
  have hfg : (stdLattice E 1).FG := Submodule.fg_pi fun _ => by
    rw [← Submodule.one_eq_range]; exact Submodule.fg_unit 1
  have h1 : (fun _ : Fin 1 => y) ∈ latHat F E (stdLattice E 1 : Set _) :=
    (mem_latHat_iff hfg _).2 fun w => mem_latLoc_stdLattice.2 fun _ => h w
  generalize hA : AddSubgroup.closure {y : Af F ⊗[F] E | ∃ a ∈ intAf F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)} = A
  have hA' : ∀ a ∈ intAf F, ∀ x : 𝓞 E, a ⊗ₜ[F] (x : E) ∈ A := fun a ha x => hA ▸ AddSubgroup.subset_closure ⟨a, ha, x, rfl⟩
  have key : latHat F E (stdLattice E 1 : Set _) ≤ A.comap (Pi.evalAddMonoidHom (fun _ : Fin 1 => Af F ⊗[F] E) 0) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨b, hb, x, hx, rfl⟩
    obtain ⟨r, hr⟩ := hx 0 trivial
    change b ⊗ₜ[F] x 0 ∈ A
    rw [← hr]
    exact hA' b hb r
  exact key h1

theorem loc_of_int {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (y : Af F ⊗[F] E)
    (h : y ∈ AddSubgroup.closure {y : Af F ⊗[F] E | ∃ a ∈ intAf F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)}) (w) :
    Algebra.TensorProduct.map (evalV F w) (AlgHom.id F E) y ∈ intLoc F E w := by
  induction h using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, hb, x, rfl⟩ := hy
    exact tmul_mem_intLoc (hb w) x
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | neg y _ hy => rw [map_neg]; exact neg_mem hy

theorem exists_mulVec_iff {R : Type} [CommRing R] {n : ℕ} (M : GL (Fin n) R) (P : (Fin n → R) → Prop) (w : Fin n → R) :
    (∃ x, P x ∧ M.1 *ᵥ x = w) ↔ P ((M⁻¹).1 *ᵥ w) := by
  constructor
  · rintro ⟨x, hx, e⟩
    rwa [← e, mulVec_mulVec, Units.inv_mul, one_mulVec]
  · exact fun H => ⟨_, H, by rw [mulVec_mulVec, Units.mul_inv, one_mulVec]⟩

variable {D : D7}

theorem int_iff_loc {v : Pl D} {a : AE D} (ha : a ∈ idAt D (· = v)) :
    a ∈ intAt D (· = v) ↔ compAt D v a ∈ intLoc D.host.F D.host.E v := by
  refine ⟨fun h => loc_of_int _ h.2 v, fun h => ⟨ha, int_of_loc _ fun w => ?_⟩⟩
  by_cases e : w = v
  · subst e; exact h
  · have h0 : compAt D w a = 0 := compAt_of_idAt ha e
    change compAt D w a ∈ _
    rw [h0]
    exact zero_mem _

theorem line_loc (V : HSp D) (Λ : Lat V) (hΛ : Λ.FG) (v : Pl D) (g : GA D V) (y₀ : Fin V.rank → AE D)
    (h : ∀ a ∈ idAt D (· = v), mt V g⁻¹ *ᵥ (a • y₀) ∈ GlobalTheory.FinPl.latV V Λ (· = v) ↔ a ∈ intAt D (· = v))
    (c : Fv D.host.F v ⊗[D.host.F] D.host.E) :
    (∃ x ∈ latLoc D.host.F Λ v, (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig V.gram (proj D.sp.cm.sig V.gram v g)).1 *ᵥ x =
      c • vecLoc v (finPart D ∘ y₀)) ↔ c ∈ intLoc D.host.F D.host.E v := by
  obtain ⟨a, ha, hc⟩ := GlobalTheory.StMoves.exists_supp_vecLoc_eq (n := 1) v fun _ => c
  have hc' : compAt D v (a 0) = c := congrFun hc 0
  have hs : ∀ i, (a 0 • y₀) i ∈ idAt D (· = v) := fun i => Ideal.mul_mem_right _ _ (ha 0)
  have e : vecLoc v (finPart D ∘ (a 0 • y₀)) = c • vecLoc v (finPart D ∘ y₀) := by
    funext i
    rw [← hc']
    exact map_mul (compAt D v) (a 0) (y₀ i)
  have key : ∀ (g : GA D V) y, vecLoc v (finPart D ∘ (mt V g *ᵥ y)) =
      (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig V.gram (proj D.sp.cm.sig V.gram v g)).1 *ᵥ vecLoc v (finPart D ∘ y) := fun g y => by
    rw [GlobalTheory.FinPl.KOpen.fin_mulVec]
    exact vecLoc_mulVec D.sp.cm.sig V.gram v g _
  rw [← hc', ← int_iff_loc (ha 0), ← h _ (ha 0), hc',
    GlobalTheory.StMoves.mem_latV_iff_latLoc V Λ hΛ v _ (GlobalTheory.FinPl.KOpen.supp_mulVec V _ _ hs), key, e, map_inv, map_inv]
  exact exists_mulVec_iff _ (· ∈ latLoc D.host.F Λ v) _

end Loc

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
open Matrix GlobalTheory.GoodPos

section Word

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D} {u : D.what₂.Word}
  {ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ℂ}

theorem xu_fixes (hE : IdE X) (r : Fin D.R.rS) :
    mt (D.sp.Y 0) ((iotaX X h).symm (1, X.xu u)) *ᵥ ratV (fun k => X.ιE (X.eR r (Fin.cast (rank_eq X h) k))) =
      ratV fun k => X.ιE (X.eR r (Fin.cast (rank_eq X h) k)) := by
  have h1 := (GlobalTheory.Core.SBesLevi.transport_fix D X.B.I X.ιE hE h (rank_eq X h) {X.eR r}
    (Formalism.IndefR.RationalEmbedding.iota D ((iotaX X h).symm (1, X.xu u)))).1
  have e : castGA h.symm (Formalism.IndefR.RationalEmbedding.iota D ((iotaX X h).symm (1, X.xu u))) = (1, X.xu u) :=
    (iotaX X h).apply_symm_apply _
  rw [e] at h1
  refine (GlobalTheory.Core.SBesLevi.bridge_fix D _ _).2 (h1 ⟨?_, ?_⟩ _ rfl)
  · exact one_mem _
  · rintro _ rfl
    exact (X.xu_fix u r).1

theorem first_vec (F₀ : Formalism.L2.Forms.Forms0 D u) (tr : Formalism.L2.SG.ColDict.Transport X u F₀) (hE : IdE X)
    (hψ : IsStdChar D ψ (-1)) (B : SBes X h u ψ (D.sp.X 0)) {μ : D.host.E} (hμ : μ ≠ 0)
    (hz : ∀ k, (B.d.i₀ *ᵥ vecB B.o B.ζ) k = μ * X.ιE (X.zR u (Fin.cast (rank_eq X h) k))) (r : Fin D.R.rS) (hr : r.1 = 0) :
    ∃ s : D.host.E, (s = 1 ∨ s = -1) ∧
      ∀ k, B.d.e k r = s * (μ * (X.B.g : D.host.E) ^ D.R.rS) * X.ιE (X.eR r (Fin.cast (rank_eq X h) k)) := by
  obtain ⟨lam, hl, H⟩ := exists_sBes_scaled_dual D X h u ψ F₀ tr hE hψ
  obtain ⟨B', -, -, hz', he, -⟩ := H μ B.vA hμ
  have hne : ∀ B : SBes X h u ψ (D.sp.X 0), vecB B.o B.ζ ≠ 0 := fun B e => besVec_ne_zero B (by rw [e, mulVec_zero])
  have h1 := GlobalTheory.FirstVec.first_eq hψ B'.d B.d (funext fun k => (hz' k).trans (hz k).symm) (hne B') (hne B)
    (fun n => (B'.tieN n).trans (B.tieN n).symm)
    (fun n hn => star_injective ((B'.tieψ n hn).trans (B.tieψ n ((B.tieN n).2 ((B'.tieN n).1 hn))).symm)) r hr
  rcases hl with rfl | rfl
  · exact ⟨1, Or.inl rfl, fun k => by rw [h1, he, hr, Nat.sub_zero, one_mul]⟩
  · exact ⟨(-1) ^ D.R.rS, neg_one_pow_eq_or _ _, fun k => by rw [h1, he, hr, Nat.sub_zero, neg_pow]; ring⟩

end Word

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}

theorem single (W : RealPack ex) (hW : PkHyp W) (r : Fin D.R.rS) (hr : r.1 = 0) {u : D.what₂.Word} (f : FamCh W u)
    (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) (hP : PlacedP f B) (a₀ a₁ : GA D (D.sp.X 0)) (x : GlobalTheory.FinPl.Pl D)
    (hg : ∀ PP ∈ (pk W).Pg, PP.under (𝓞 D.host.F) ≠ x) (hx : (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∉ x.asIdeal) {α cc : (AE D)ˣ}
    (hα : ∀ (S : Formalism.BasicNotions.TH.HSp D) (L : GlobalTheory.FinPl.Lat S) y,
      y ∈ latA S L (· = x) ↔ ((α⁻¹ : (AE D)ˣ) : AE D) • y ∈ latV S L (· = x))
    (hψ : ∀ s ∈ idAt D (· = x), (∀ o ∈ intAt D (· = x), psiE W.Q.Rl.ψ (s * o) = 1) ↔
      ((cc⁻¹ : (AE D)ˣ) : AE D) * s ∈ intAt D (· = x)) :
    ∀ a ∈ idAt D (· = x), mt (D.sp.Y 0) (tOf f B a₀ a₁)⁻¹ *ᵥ (a •
      (((cc ^ (D.R.rS - 1) * (α * α * (α * (xiU D * cU α)⁻¹) ^ D.R.rS) : (AE D)ˣ) : AE D) *
        incA D (D.host.xi0 ^ (D.R.m / 2) * (W.S.X.B.g : D.host.E) ^ D.R.rS)) •
      ratV fun k => W.S.X.ιE (W.S.X.eR r (Fin.cast (rank_eq W.S.X W.Q.instEq) k))) ∈ latV (D.sp.Y 0) ((pk W).ΛY 0) (· = x) ↔
      a ∈ intAt D (· = x) := by
  intro a ha
  obtain ⟨k, i1, i2, i3, i4, ι, v, o, n, G, pl, hc, -, ht, sh, -, -, hb, hp⟩ := hP
  obtain ⟨μ, lam, n1, n2, n3⟩ := hb.norm
  have hξ : -D.host.xi0 ^ (D.R.m / 2) ≠ 0 := neg_ne_zero.2 (pow_ne_zero _ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D))
  have hμ : μ ≠ 0 := left_ne_zero_of_mul (n1 ▸ hξ)
  have hlam : lam ≠ 0 := right_ne_zero_of_mul (n1 ▸ hξ)
  have h₀ : 0 + 2 * D.R.rS + 2 = D.R.m := by
    obtain ⟨c, hc⟩ := D.R.m_even
    have := D.R.two_le_m
    unfold Ranks.rS
    omega
  obtain ⟨s, hs, he⟩ := first_vec (F0 W u) (W.S.tr u) hW.bot.idE hc.std B hμ n2 r hr
  have hI := all_ideal hc sh (fun n h x hx => by subst h; exact hp x hx) (fun j hj => by
      change 0 < (D.sp.X (j + 1)).rank
      rw [Formalism.L2.Forms.rankN D _ hj]
      unfold Ranks.N
      have := D.R.m_add_three_le_k
      omega) hlam n3 (fun e => hx ((ht.tP x).1 e)) hα hψ 0 D.R.rS h₀ (D.R.rS - 1) r (by have := r.2; omega)
  have hd : B.d.e = (f.c.bes 0 D.R.rS h₀).d.e := eq_of_heq (Sigma.mk.inj (congrArg
    (fun Z : BesLev D D.R.rS => (⟨Z.V.rank, Z.d.e⟩ : Σ n, Matrix (Fin n) (Fin D.R.rS) D.host.E)) (hb.lev h₀))).2
  have hm := ht.moves 0 (by omega) (· = x) fun p hp e => by
    obtain ⟨PP, h1, h2⟩ := (ht.gP p).1 e
    exact hg PP h1 (h2.symm.trans hp)
  have hx1 := xu_fixes (h := W.Q.instEq) (u := u) hW.bot.idE r
  rw [← mul_assoc (α * α), ← mul_assoc (cc ^ _)] at hI
  generalize cc ^ (D.R.rS - 1) * (α * α * (α * (xiU D * cU α)⁻¹) ^ D.R.rS) = K at hI ⊢
  obtain ⟨ε, hε⟩ : ∃ ε : Fin (D.sp.Y 0).rank → D.host.E,
      (fun k => W.S.X.ιE (W.S.X.eR r (Fin.cast (rank_eq W.S.X W.Q.instEq) k))) = ε := ⟨_, rfl⟩
  have he' : ∀ k, B.d.e k r = s * (μ * (W.S.X.B.g : D.host.E) ^ D.R.rS) * ε k := fun k => by rw [he, ← hε]
  rw [hε] at hx1 ⊢
  have hss : s * s = 1 := by rcases hs with rfl | rfl <;> simp
  have hy : a • ((K : AE D) * incA D (D.host.xi0 ^ (D.R.m / 2) * (W.S.X.B.g : D.host.E) ^ D.R.rS)) • ratV ε =
      colMul B.d.jX r ((K : AE D) * incA D lam * (incA D (-s) * a)) := by
    funext k
    change a * (_ * incA D (ε k)) = _ * incA D (B.d.e k r)
    have : D.host.xi0 ^ (D.R.m / 2) * (W.S.X.B.g : D.host.E) ^ D.R.rS * ε k = lam * -s * B.d.e k r := by
      rw [he']
      linear_combination ((W.S.X.B.g : D.host.E) ^ D.R.rS * ε k) * n1 + (lam * μ * (W.S.X.B.g : D.host.E) ^ D.R.rS * ε k) * hss
    have h2 := congrArg (incA D) this
    rw [map_mul, map_mul (incA D) (lam * -s), map_mul (incA D) lam] at h2
    linear_combination (a * K) * h2
  have hfix : mt (D.sp.Y 0) ((show GA D (D.sp.Y 0) from f.g.b 0) * (tOf f B a₀ a₁)⁻¹) *ᵥ
      (a • ((K : AE D) * incA D (D.host.xi0 ^ (D.R.m / 2) * (W.S.X.B.g : D.host.E) ^ D.R.rS)) • ratV ε) =
      colMul B.d.jX r ((K : AE D) * incA D lam * (incA D (-s) * a)) := by
    have e : (show GA D (D.sp.Y 0) from f.g.b 0) * (tOf f B a₀ a₁)⁻¹ =
        embA B.d B.o (a₀ * a₁)⁻¹ * (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) := by
      unfold tOf
      rw [map_inv, _root_.mul_inv_rev, mul_inv_cancel_left, _root_.mul_inv_rev, inv_inv]
    rw [e, GlobalTheory.MixModel.mt_mul, ← mulVec_mulVec, mulVec_smul (mt _ ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))), mulVec_smul (mt _ ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))), hx1, hy]
    generalize (K : AE D) * incA D lam * (incA D (-s) * a) = t
    have e1 : colMul B.d.jX r t = B.d.jX *ᵥ Pi.single r t := by
      rw [mulVec_single]; funext k; exact mul_comm _ _
    rw [e1, mulVec_mulVec, embA_apply, B.d.wittDecomp_anisotropicEmbedding_inclX]
  have hsup : ∀ i, (a • ((K : AE D) * incA D (D.host.xi0 ^ (D.R.m / 2) * (W.S.X.B.g : D.host.E) ^ D.R.rS)) • ratV ε) i ∈
      idAt D (· = x) := fun i => Ideal.mul_mem_right _ _ ha
  rw [GlobalTheory.MixModel.mt_mul, ← mulVec_mulVec] at hfix
  have hj : B.d.jX = (f.c.bes 0 D.R.rS h₀).d.jX := congrArg rat hd
  have h1 := hI ((K : AE D) * incA D lam * (incA D (-s) * a)) (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ ha))
  rw [← inU_val lam hlam, ← Units.val_mul, Units.inv_mul_cancel_left, Units.val_mul, inU_val, ← hj] at h1
  refine (hm _ (GlobalTheory.FinPl.KOpen.supp_mulVec (D.sp.Y 0) _ _ hsup)).trans
    ((iff_of_eq (congrArg (· ∈ latV (D.sp.Y 0) (v.N 0) (· = x)) hfix)).trans (h1.trans ?_))
  rcases hs with rfl | rfl
  · rw [map_neg, map_one, neg_one_mul, int_neg]
  · rw [neg_neg, map_one, one_mul]

theorem common_line : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → 1 ≤ D.R.rS → ∀ u u' (f : FamCh W u) (f' : FamCh W u') (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) (B' : SBes W.S.X W.Q.instEq u' W.Q.Rl.ψ (D.sp.X 0)), GlobalTheory.MiTop.PlacedP f B → GlobalTheory.MiTop.PlacedP f' B' → ∀ a₀ a a₀' a', IsAt f B a₀ a → IsAt f' B' a₀' a' → ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (∀ PP ∈ (pk W).Pg, PP.under (𝓞 D.host.F) ≠ v) → (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal → (((D.mem u').A.T : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal → ∃ w : Fin (D.sp.Y 0).rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E, ∀ c : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E, ((∃ x ∈ GlobalTheory.AdelicU.latLoc D.host.F ((pk W).ΛY 0) v, Matrix.mulVec (GlobalTheory.AdelicU.matHom (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) D.sp.cm.sig (D.sp.Y 0).gram (GlobalTheory.AdelicU.proj D.sp.cm.sig (D.sp.Y 0).gram v (tOf f B a₀ a))).1 x = c • w) ↔ c ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v) ∧ ((∃ x ∈ GlobalTheory.AdelicU.latLoc D.host.F ((pk W).ΛY 0) v, Matrix.mulVec (GlobalTheory.AdelicU.matHom (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) D.sp.cm.sig (D.sp.Y 0).gram (GlobalTheory.AdelicU.proj D.sp.cm.sig (D.sp.Y 0).gram v (tOf f' B' a₀' a'))).1 x = c • w) ↔ c ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v) := by
  intro D L hT Gi Gl Kc Yd cX ex W hW hr u u' f f' B B' hP hP' a₀ a a₀' a' _ _ v hg hu hu'
  have hstd : IsStdChar D W.Q.Rl.ψ (-1) := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hc, -⟩ := hP
    exact hc.std
  obtain ⟨α, hα⟩ := GlobalTheory.IdeleAA.exists_idele_AA D _ hstd
  have hψ : ∀ s ∈ idAt D (· = v), (∀ o ∈ intAt D (· = v), psiE W.Q.Rl.ψ (s * o) = 1) ↔
      (((xiU D * α * cU α)⁻¹ : (AE D)ˣ) : AE D) * s ∈ intAt D (· = v) := fun s hs => by
    rw [(hα v).2 s hs, mul_inv, mul_inv, Units.val_mul, Units.val_mul, cU_inv, xiU, inU_inv]
  have hfg : ((pk W).ΛY 0).FG := (sdY_frames W hW 0 (by have := D.R.two_le_m; omega)).1.1.fg
  exact ⟨_, fun c => ⟨line_loc (D.sp.Y 0) _ hfg v _ _ (single W hW ⟨0, hr⟩ rfl f B hP a₀ a v hg hu (hα v).1 hψ) c,
    line_loc (D.sp.Y 0) _ hfg v _ _ (single W hW ⟨0, hr⟩ rfl f' B' hP' a₀' a' v hg hu' (hα v).1 hψ) c⟩⟩

end GlobalTheory.LineIdeal

end
