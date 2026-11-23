import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemFinPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTranspAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CombineApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedCmDataStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewSpaceDetNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianFormIntegralLatticeExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanSkewHermitianNormalFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleRingInfiniteFiniteSplitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanNormalFormUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanNormalFormLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeUnitaryNormalFormStatement

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Matrix TensorProduct

namespace GlobalTheory.ThKUTr

theorem glueM_sub_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (Φ : AE F E ≃+* (InfinitePlace F → ℂ) × (E ⊗[F] Formalism.MainNotions.S.Af F)) {n : ℕ}
    (p : (InfinitePlace F → Matrix (Fin n) (Fin n) ℂ) × Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.MainNotions.S.Af F)) (i j : Fin n) :
    Φ ((GlobalTheory.ThKUTr.glueM Φ n p - 1) i j) = (fun w => (p.1 w - 1) i j, (p.2 - 1) i j) := by
  rw [← map_one (GlobalTheory.ThKUTr.glueM Φ n), ← map_sub, GlobalTheory.ThKUTr.glueM_apply, RingEquiv.apply_symm_apply]
  rfl

theorem glueM_comp {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (Φ : AE F E ≃+* (InfinitePlace F → ℂ) × (E ⊗[F] Formalism.MainNotions.S.Af F)) {n : ℕ}
    (p : (InfinitePlace F → Matrix (Fin n) (Fin n) ℂ) × Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.MainNotions.S.Af F)) (i j : Fin n) :
    Φ (GlobalTheory.ThKUTr.glueM Φ n p i j) = (fun w => p.1 w i j, p.2 i j) := by
  rw [GlobalTheory.ThKUTr.glueM_apply, RingEquiv.apply_symm_apply]

end GlobalTheory.ThKUTr

namespace GlobalTheory.ThKUTr

section Fields

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {W : Spc F E n} {Φ : AE F E ≃+* (InfinitePlace F → ℂ) × (E ⊗[F] Formalism.MainNotions.S.Af F)} {ε : InfinitePlace F → Fin n → Bool}
  {P : InfinitePlace F → (Matrix (Fin n) (Fin n) ℂ)ˣ} {H : Subgroup (GL (Fin n) (E ⊗[F] Formalism.MainNotions.S.Af F))}
  (hU : ∀ x, GlobalTheory.ThKUTr.rawT Φ ε P H x ∈ UG (cA σ) (incM F W.J))

include hU

theorem trHom_real (hΦ : ∀ (u : AF F) z, evI F u = 0 → (Φ z).2 = 0 → u • z = 0)
    (x : ∀ v : InfinitePlace F, Formalism.REAL.UJ (ε v)) :
    GlobalTheory.ThKUTr.trHom σ W.J Φ ε P H hU (x, 1) ∈ UAt σ W (evI F) := by
  intro u hu
  ext i j
  rw [Matrix.smul_apply, Matrix.zero_apply]
  refine hΦ u _ hu ?_
  rw [GlobalTheory.ThKUTr.mat_trHom, GlobalTheory.ThKUTr.rawT_val, glueM_sub_one]
  simp

theorem trHom_fin (hΦ : ∀ (u : AF F) z, u.2 = 0 → (Φ z).1 = 0 → u • z = 0) (k : H) :
    At (fun a : AF F => a.2) (mat (GlobalTheory.ThKUTr.trHom σ W.J Φ ε P H hU (1, k)) - 1) := by
  intro u hu
  ext i j
  rw [Matrix.smul_apply, Matrix.zero_apply]
  refine hΦ u _ hu ?_
  rw [GlobalTheory.ThKUTr.mat_trHom, GlobalTheory.ThKUTr.rawT_val, glueM_sub_one]
  funext w
  show (((P w : Matrix (Fin n) (Fin n) ℂ) * Formalism.MainNotions.S.uMat ((1 : ∀ v : InfinitePlace F, Formalism.REAL.UJ (ε v)) w) *
    (((P w)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) - 1) i j = 0
  rw [show Formalism.MainNotions.S.uMat ((1 : ∀ v : InfinitePlace F, Formalism.REAL.UJ (ε v)) w) = 1 from rfl, Matrix.mul_one, Units.mul_inv,
    sub_self, Matrix.zero_apply]

theorem trHom_frame (B : Base F E) (hΦ : ∀ z w, (Φ z).1 w = piInf (B.emb w) z)
    (x : ∀ v : InfinitePlace F, Formalism.REAL.UJ (ε v)) (v : InfinitePlace F) :
    (mat (GlobalTheory.ThKUTr.trHom σ W.J Φ ε P H hU (x, 1))).map (piInf (B.emb v)) =
      (P v : Matrix (Fin n) (Fin n) ℂ) * Formalism.MainNotions.S.uMat (x v) * ((P v)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) := by
  ext i j
  rw [Matrix.map_apply, ← hΦ, GlobalTheory.ThKUTr.mat_trHom, GlobalTheory.ThKUTr.rawT_val, glueM_comp]

theorem trHom_rat (B : Base F E)
    (hΦ : ∀ x : E, Φ (inclR (F := F) (AF F) x) = (fun w => (B.emb w).1 x, Formalism.UG.inclE (F := F) (Formalism.MainNotions.S.Af F) x))
    (γ : GL (Fin n) E) (x : ∀ v : InfinitePlace F, Formalism.REAL.UJ (ε v)) (y : H)
    (hx : ∀ v, Formalism.MainNotions.S.uMat (x v) = (P v : Matrix (Fin n) (Fin n) ℂ)⁻¹ * (γ : Matrix (Fin n) (Fin n) E).map (B.emb v).1 *
      (P v : Matrix (Fin n) (Fin n) ℂ))
    (hy : ((y : GL (Fin n) (E ⊗[F] Formalism.MainNotions.S.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.MainNotions.S.Af F)) =
      (γ : Matrix (Fin n) (Fin n) E).map (Formalism.UG.inclE (F := F) (Formalism.MainNotions.S.Af F))) :
    GlobalTheory.ThKUTr.trHom σ W.J Φ ε P H hU (x, y) ∈ ratU σ W.J := by
  rw [ratU, Subgroup.mem_subgroupOf]
  refine ⟨γ, Units.ext ?_⟩
  ext i j
  show inclR (F := F) (AF F) ((γ : Matrix (Fin n) (Fin n) E) i j) = mat (GlobalTheory.ThKUTr.trHom σ W.J Φ ε P H hU (x, y)) i j
  rw [GlobalTheory.ThKUTr.mat_trHom, GlobalTheory.ThKUTr.rawT_val, GlobalTheory.ThKUTr.glueM_apply, RingEquiv.eq_symm_apply, hΦ]
  refine Prod.ext (funext fun w => ?_) ?_
  · show (B.emb w).1 _ = ((P w : Matrix (Fin n) (Fin n) ℂ) * Formalism.MainNotions.S.uMat (x w) * ((P w)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ)) i j
    have hdet : IsUnit (P w : Matrix (Fin n) (Fin n) ℂ).det := (Matrix.isUnit_iff_isUnit_det _).1 (P w).isUnit
    rw [hx w, Matrix.coe_units_inv, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet,
      Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one, Matrix.map_apply]
  · show _ = ((y : GL (Fin n) (E ⊗[F] Formalism.MainNotions.S.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.MainNotions.S.Af F)) i j
    rw [hy]
    rfl

theorem trHom_kinf (B : Base F E) (hΦr : ∀ (u : AF F) z, evI F u = 0 → (Φ z).2 = 0 → u • z = 0)
    (hΦ : ∀ z w, (Φ z).1 w = piInf (B.emb w) z)
    (hθ : ∀ w, ∃ c : ℂ, c ≠ 0 ∧ (P w : Matrix (Fin n) (Fin n) ℂ) * Formalism.REAL.Jm (ε w) = c • (W.θ w * (P w : Matrix (Fin n) (Fin n) ℂ)))
    (k : ∀ v : InfinitePlace F, Formalism.REAL.KG (ε v)) :
    GlobalTheory.ThKUTr.trHom σ W.J Φ ε P H hU (fun v => (k v : Formalism.REAL.UJ (ε v)), 1) ∈ KInf σ W B.emb := by
  refine ⟨trHom_real hU hΦr _, fun w => ?_⟩
  rw [trHom_frame hU B hΦ]
  obtain ⟨c, hc, hPc⟩ := hθ w
  have hk : Formalism.MainNotions.S.uMat ((k w : Formalism.REAL.UJ (ε w))) * Formalism.REAL.Jm (ε w) =
      Formalism.REAL.Jm (ε w) * Formalism.MainNotions.S.uMat ((k w : Formalism.REAL.UJ (ε w))) := (k w).2.2
  have e1 : (((P w)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) * (P w : Matrix (Fin n) (Fin n) ℂ) = 1 :=
    Units.inv_mul (P w)
  have e2 : (P w : Matrix (Fin n) (Fin n) ℂ) * (((P w)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = 1 :=
    Units.mul_inv (P w)
  have hθw : W.θ w = c⁻¹ • ((P w : Matrix (Fin n) (Fin n) ℂ) * Formalism.REAL.Jm (ε w) *
      (((P w)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) := by
    rw [hPc, Matrix.smul_mul, Matrix.mul_assoc, e2, Matrix.mul_one, smul_smul, inv_mul_cancel₀ hc, one_smul]
  rw [hθw]
  refine Commute.smul_right ?_ _
  show _ * _ = _ * _
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (((P w)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ), e1, Matrix.one_mul,
    ← Matrix.mul_assoc (((P w)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ), e1, Matrix.one_mul,
    ← Matrix.mul_assoc (Formalism.MainNotions.S.uMat _), hk, Matrix.mul_assoc]

end Fields

end GlobalTheory.ThKUTr

namespace GlobalTheory.ThKUTr

theorem exists_transport : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∀ (L : Subgroup (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J)), GlobalTheory.ThKAdm.IsLevel G.W L → ∃ (I : Formalism.MainNotions.S.AutInst) (g : ℕ) (e : I.GA →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J), 1 ≤ g ∧ GlobalTheory.ThKAdm.IsTransp B G.W L I g e := by
  intro _ F E _ _ _ _ _ σ B a a' G X om om' R Rf hM L hL
  have hB := hM.triple.base
  have hG := hM.triple.geo
  have hW := hG.hW
  have hcm := hB.cm
  obtain ⟨w₀⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hσ : ∀ x, σ (σ x) = x := fun x => by
    apply (B.emb w₀).1.injective
    rw [hcm.2.2.2, hcm.2.2.2, star_star]
  letI : StarRing E := GlobalTheory.ThKUTr.starOf σ hσ
  have cm : Formalism.BasicNotions.CMData F E := GlobalTheory.T.unramified_cm_data F E σ hσ hcm hB.unram
  have hsig : cm.sig = σ := AlgHom.ext fun _ => rfl
  have hstar : starRingEnd E = (σ : E →+* E) := RingHom.ext fun _ => rfl
  obtain ⟨δ, hδ, hδ0⟩ : ∃ δ : E, σ δ = -δ ∧ δ ≠ 0 := by
    obtain ⟨c, hc0, hc⟩ := GlobalTheory.AdelicU.exists_integer_conj_eq_neg hcm
    exact ⟨(c : E), hc, fun h => hc0 (by exact_mod_cast h)⟩
  obtain ⟨-, Lat, hLfg, hLs, hLd⟩ := GlobalTheory.T.skew_hermitian_form_integral_lattice_exists F E σ B (a + a') _ _ G.W hB hW hG.even δ hδ0 hδ
  have hJd := GlobalTheory.T.skew_space_det_ne_zero F E σ B (a + a') _ _ G.W hW
  set J' : Matrix (Fin (a + a')) (Fin (a + a')) E := δ • G.W.J.map σ with hJ'
  have hH : Formalism.UG.IsHerm (starRingEnd E) J' := by
    ext i j
    show σ (δ * σ (G.W.J j i)) = δ * σ (G.W.J i j)
    rw [map_mul, hσ, hδ, hW.skew j i]
    ring
  have hJ'd : J'.det ≠ 0 := by
    rw [hJ', Matrix.det_smul]
    refine mul_ne_zero (pow_ne_zero _ hδ0) ?_
    have : (G.W.J.map σ).det = σ G.W.J.det := ((σ : E →+* E).map_det G.W.J).symm
    rw [this]
    exact fun h => hJd (by rw [← hσ G.W.J.det, h, map_zero])
  have hfr : ∀ w : InfinitePlace F, ∃ (ε : Fin (a + a') → Bool) (P : Matrix (Fin (a + a')) (Fin (a + a')) ℂ),
      IsUnit P ∧ Pᴴ * J'.map (B.emb w).1 * P = Formalism.REAL.Jm ε ∧
        ∃ c : ℂ, c ≠ 0 ∧ P * Formalism.REAL.Jm ε = c • (G.W.θ w * P) := by
    intro w
    have hmap : J'.map (B.emb w).1 = (B.emb w).1 δ • (G.W.J.map (B.emb w).1).map star := by
      ext i j
      simp [J', hcm.2.2.2]
    rw [hmap]
    refine GlobalTheory.T.cartan_skew_hermitian_normal_form _ (G.W.J.map (B.emb w).1) (G.W.θ w) ((B.emb w).1 δ) ?_ ?_ ?_ (hW.cartan w)
    · rw [← hcm.2.2.2, hδ, map_neg]
    · exact fun h => hδ0 ((B.emb w).1.injective (by rw [h, map_zero]))
    · intro i j
      simp only [Matrix.map_apply]
      rw [← hcm.2.2.2, hW.skew, map_neg]
  choose ε P hPu hPs hPθ using hfr
  let I : Formalism.MainNotions.S.AutInst := GlobalTheory.AutInhab.ofFrames cm (a + a') J' hH hJ'd Lat hLs hLfg (hstar ▸ hLd) ε
    (fun w => (B.emb w).1) (fun w x => RingHom.congr_fun (B.emb w).2 x) P hPu hPs
  obtain ⟨Φ, hΦ1, hΦ2, hΦ3, hΦ4, hΦ5, hΦ6, hΦ7⟩ := GlobalTheory.T.adele_ring_infinite_finite_split F E σ B hcm
  let Pu : InfinitePlace F → (Matrix (Fin (a + a')) (Fin (a + a')) ℂ)ˣ := fun w => (hPu w).unit
  have hU := GlobalTheory.T.archimedean_normal_form_unitary F E σ B (a + a') G.W.J δ Φ ε Pu hcm hδ hδ0 hW.skew hΦ1 hΦ3 hPs
  let e : I.GA →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J := GlobalTheory.ThKUTr.trHom σ G.W.J Φ ε Pu _ hU
  have hcont : Continuous e := GlobalTheory.T.lattice_unitary_normal_form F E σ (a + a') G.W.J J' Φ ε Pu Lat hLs hLfg hU hΦ6 hΦ7
  obtain ⟨hLfin, U, hUo, hU1, hUL⟩ := hL
  have hpre : {y : I.Gf | e (1, y) ∈ U} ∈ nhds (1 : I.Gf) := by
    have hc : Continuous fun y : I.Gf => e (1, y) := hcont.comp (continuous_const.prodMk continuous_id)
    refine hc.continuousAt.preimage_mem_nhds ?_
    have h1 : e (1, 1) = 1 := map_one e
    rw [h1]
    exact hUo.mem_nhds hU1
  obtain ⟨g, hg, hgsub⟩ := I.topf_basis _ hpre
  refine ⟨I, g, e, hg, ⟨GlobalTheory.T.archimedean_normal_form_lattice F E σ B (a + a') G.W.J δ Φ ε Pu hcm hδ hδ0 hW.skew hΦ1 hΦ3 hPs hU, hcont, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rintro ⟨x, y⟩ ⟨γ, -, hx, hy⟩
    exact trHom_rat hU B hΦ1 γ x y hx hy
  · intro k hk
    exact hUL ⟨hgsub hk, trHom_fin hU hΦ5 k⟩
  · intro k
    exact trHom_kinf hU B hΦ4 hΦ2 hPθ k
  · intro x
    exact trHom_real hU hΦ4 x
  · exact ⟨Equiv.refl _, fun v => (Pu v : Matrix (Fin (a + a')) (Fin (a + a')) ℂ),
      fun v => (((Pu v)⁻¹ : (Matrix (Fin (a + a')) (Fin (a + a')) ℂ)ˣ) : Matrix (Fin (a + a')) (Fin (a + a')) ℂ), fun v => ⟨Units.inv_mul _, Units.mul_inv _⟩,
      fun x v => trHom_frame hU B hΦ2 x v⟩

end GlobalTheory.ThKUTr
