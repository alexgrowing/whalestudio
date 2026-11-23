import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmulLk
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 4000000

namespace GlobalTheory.Mem.Col2.HAt.Stab

theorem co_apply {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) {n : ℕ} (h : S.rank = n)
    (g : S.V ≃ₗ[E] S.V) (x : S.V) :
    co S h (g x) = (reGL h E (Formalism.L2.Herm.toGLb S.frame g)).1 *ᵥ co S h x := by
  have e : lin S h (reGL h E (Formalism.L2.Herm.toGLb S.frame g)) = g := by
    subst h
    have e0 : ∀ k : GL (Fin S.rank) E, reGL rfl E k = k := fun k => by
      ext a b
      simp [reGL]
    show (Formalism.L2.Herm.toGLb S.frame).symm (reGL rfl E (reGL rfl E (Formalism.L2.Herm.toGLb S.frame g))) = g
    rw [e0, e0, MulEquiv.symm_apply_apply]
  rw [← co_lin, e]

theorem co_symm_apply {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) {n : ℕ} (h : S.rank = n)
    (k : GL (Fin S.rank) E) (x : S.V) :
    co S h ((Formalism.L2.Herm.toGLb S.frame).symm k x) = (reGL h E k).1 *ᵥ co S h x := by
  rw [co_apply, MulEquiv.apply_symm_apply]

theorem eq_of_frMul {E K ι : Type} [Field E] [Field K] [Fintype ι] (τ : ι) (emb : ι → E →+* K) (σ : K →+* ℂ) {n : ℕ}
    (g M : GL (Fin n) E) (y : Col2.Fr emb σ n) (h : frMul emb σ M⁻¹ (frMul emb σ g y) = y) : g = M := by
  have h1 : (M⁻¹ : GL (Fin n) E).1.map (embAt σ emb τ) * (g.1.map (embAt σ emb τ) * y.1 τ) = y.1 τ :=
    congrFun (congrArg Subtype.val h) τ
  rw [← Matrix.mul_assoc, ← Matrix.map_mul, ← Units.val_mul] at h1
  have hy : IsUnit (y.1 τ) := (Matrix.isUnit_iff_isUnit_det _).2 (y.2 τ)
  have h2 : (M⁻¹ * g : GL (Fin n) E).1.map (embAt σ emb τ) = 1 := hy.mul_right_cancel (by rw [h1, Matrix.one_mul])
  have h3 : (M⁻¹ * g : GL (Fin n) E).1 = 1 := by
    apply Matrix.map_injective (embAt σ emb τ).injective
    show _ = (1 : Matrix (Fin n) (Fin n) E).map (embAt σ emb τ)
    rw [Matrix.map_one _ (map_zero _) (map_one _)]
    exact h2
  have h4 : M⁻¹ * g = 1 := Units.ext h3
  exact (inv_mul_eq_one.1 h4).symm

theorem ext_vec {E : Type} [Field E] {N n : ℕ} (hN : N = n + 1) {x y : Fin N → E} (h1 : iniH hN x = iniH hN y)
    (h2 : x (Br.iL hN) = y (Br.iL hN)) : x = y := by
  funext j
  by_cases hj : j.1 < n
  · exact congrFun h1 ⟨j.1, hj⟩
  · have : j = Br.iL hN := Fin.ext (by have := j.2; show j.1 = n; omega)
    rw [this, h2]

theorem ga_eq_gam_mv : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u)) → ∀ (u : B.Word) (c : ((I.rec7 l Z).fm u).clsP), ((F u).til.ga c).1.1 = ((I.stp u I.mu0 B.R.m).gam (I.perIn u I.mu0).b0 ((I.stp u I.mu0 B.R.m).mv (I.perIn u I.mu0).b0 ((I.perIn u I.mu0).tilPt c))).1 := by
  intro B X I l Z H F hF u c
  classical
  have hemb : Formalism.L2.Forms.embT (I.rec7 l Z) = embAt B.embLL B.fields.emb := by
    funext τ
    ext y
    show B.host.φ₀ _ = _
    rw [← B.embE_φ₀]
    rfl
  let y : Col2.Fr B.fields.emb B.embLL (B.R.N B.R.m) := ⟨fun _ => 1, fun _ => by simp⟩
  let g : GL (Fin (B.R.N B.R.m)) B.fields.E := ((F u).til.ga c).1
  let φ : (I.stp u I.mu0 B.R.m).Cl → Col2.Fr B.fields.emb B.embLL (B.R.N B.R.m) → ℂ := fun _ z => if z = y then 1 else 0
  have hY := (hF u).eY B.R.m le_rfl (Or.inr rfl)
  have h := (F u).evz φ c (frMul B.fields.emb B.embLL g y) y (by
    intro τ
    rw [hemb]
    exact (congrFun (hY _) τ).trans (congrArg (fun k : Matrix (Fin (B.R.N B.R.m)) (Fin (B.R.N B.R.m)) ℂ => (g.1.map (embAt B.embLL B.fields.emb τ) * k : Matrix (Fin (B.R.N B.R.m)) (Fin (B.R.N B.R.m)) ℂ)) (congrFun (hY y) τ)).symm)
  rw [(hF u).eWz] at h
  have h' : B.embLL _ * φ ((I.perIn u I.mu0).tilC c) (frMul B.fields.emb B.embLL ((I.stp u I.mu0 B.R.m).gam (I.perIn u I.mu0).b0 ((I.stp u I.mu0 B.R.m).mv (I.perIn u I.mu0).b0 ((I.perIn u I.mu0).tilPt c)))⁻¹ (frMul B.fields.emb B.embLL g y)) = _ * φ ((I.perIn u I.mu0).tilC c) y := h
  have hy : frMul B.fields.emb B.embLL ((I.stp u I.mu0 B.R.m).gam (I.perIn u I.mu0).b0 ((I.stp u I.mu0 B.R.m).mv (I.perIn u I.mu0).b0 ((I.perIn u I.mu0).tilPt c)))⁻¹ (frMul B.fields.emb B.embLL g y) = y := by
    by_contra hne
    simp only [φ, if_neg hne, if_pos, mul_zero, mul_one] at h'
    exact Units.ne_zero _ h'.symm
  exact congrArg Units.val (eq_of_frMul (show B.fields.Tau from (I.rec7 l Z).eTau.symm 1) _ _ _ _ _ hy)

theorem crdN_stabM : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u)) → CarH H F → ∀ (u : B.Word) (h1 : 1 ≤ (I.rec7 l Z).R.m) (c : ((I.rec7 l Z).mem u).C.cls (I.rec7 l Z).R.m) (s : ((I.rec7 l Z).mem u).C.stab (I.rec7 l Z).R.m c) (y : ((I.rec7 l Z).sp.X (I.rec7 l Z).R.m).V), crdN (I.rec7 l Z) (I.rec7 l Z).R.m le_rfl (Formalism.L2.Herm.stabMLinS (I.rec7 l Z) H u h1 c s y) = ((I.stp u I.mu0 B.R.m).gam c.1 s.1).1 *ᵥ crdN (I.rec7 l Z) (I.rec7 l Z).R.m le_rfl y := by
  intro B X I l Z H F hF hC u h1 c s y
  obtain ⟨k, hk⟩ := (hF u).ends B.R.m le_rfl (Or.inr rfl)
  have e1 := hk.stab c s
  have e2 := (hC.carM u).st_eq c s
  have e3 : ∀ (β β' : H.Ch u (I.rec7 l Z).R.m) (h : H.chOf u (I.rec7 l Z).R.m c = β) (h' : H.chOf u (I.rec7 l Z).R.m c = β'),
      ((H.cls u (I.rec7 l Z).R.m h1 le_rfl β).stabI ⟨c, h⟩ s).1 = ((H.cls u (I.rec7 l Z).R.m h1 le_rfl β').stabI ⟨c, h'⟩ s).1 := by
    intro β β' h h'
    subst h
    subst h'
    rfl
  refine (co_symm_apply ((I.rec7 l Z).sp.X (I.rec7 l Z).R.m) (rankN (I.rec7 l Z) (I.rec7 l Z).R.m le_rfl) _ y).trans ?_
  refine congrArg (fun k : GL (Fin (B.R.N B.R.m)) B.fields.E => k.1 *ᵥ crdN (I.rec7 l Z) (I.rec7 l Z).R.m le_rfl y) ?_
  rw [← e1]
  exact (congrArg _ (e3 _ _ rfl (chOf_m H u c))).trans e2.symm

theorem crdP_stabP : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)) (A : ∀ u, Formalism.L2.Herm.AtT (I.rec7 l Z) u (H.vT u) (H.Fv u)), (∀ u, I.StdF l Z u (F u)) → CarT H F A → ∀ (u : B.Word) (c : ((I.rec7 l Z).fm u).clsP) (s : ((I.rec7 l Z).fm u).stabilizer₂ c) (x : (I.rec7 l Z).sp.X'.V), crdP (I.rec7 l Z) (Formalism.L2.Herm.stabPLinS (I.rec7 l Z) H A u c s x) = ((I.perIn u I.mu0).S'.gam c.1 s.1).1 *ᵥ crdP (I.rec7 l Z) x := by
  intro B X I l Z H F A hF hC u c s x
  have e1 := (hF u).what₂.stab c s
  have e2 := (hC.carP u).st_eq c s
  refine (co_symm_apply (I.rec7 l Z).sp.X' (rankP (I.rec7 l Z)) _ x).trans ?_
  exact congrArg (fun k : GL (Fin (B.R.N B.R.m - 1)) B.fields.E => k.1 *ᵥ crdP (I.rec7 l Z) x) (e2.symm.trans e1)

theorem crdN_tilG : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)) (A : ∀ u, Formalism.L2.Herm.AtT (I.rec7 l Z) u (H.vT u) (H.Fv u)), CarT H F A → ∀ (u : B.Word) (c : ((I.rec7 l Z).fm u).clsP) (y : ((I.rec7 l Z).sp.X (I.rec7 l Z).R.m).V), crdN (I.rec7 l Z) (I.rec7 l Z).R.m le_rfl (((A u).tilG c).1 y) = ((F u).til.ga c).1.1 *ᵥ crdN (I.rec7 l Z) (I.rec7 l Z).R.m le_rfl y := by
  intro B X I l Z H F A hC u c y
  rw [hC.ga u c]
  exact co_apply ((I.rec7 l Z).sp.X (I.rec7 l Z).R.m) (rankN (I.rec7 l Z) (I.rec7 l Z).R.m le_rfl) _ y

theorem gam_ext : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (b : (I.perIn u I.mu0).S'.β) (g : (I.perIn u I.mu0).S'.G b), (∀ y, ((I.stp u I.mu0 B.R.m).gam (I.perIn u I.mu0).b0 ((I.perIn u I.mu0).ext b g)).1 *ᵥ iXc (I.rec7 l Z) y = iXc (I.rec7 l Z) (((I.perIn u I.mu0).S'.gam b g).1 *ᵥ y)) ∧ ((I.stp u I.mu0 B.R.m).gam (I.perIn u I.mu0).b0 ((I.perIn u I.mu0).ext b g)).1 *ᵥ TC.z0 X u = TC.z0 X u := by
  intro B X I hOk hP l Z u b g
  have hi := (GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hOk hP l Z).2.2.1
  have ini : ∀ y : Fin (B.R.N B.R.m - 1) → B.fields.E, iniH (N_m_succ B.R) (iXc (I.rec7 l Z) y) = y := fun y => by
    funext j
    exact (hi y _).trans (dif_pos j.2)
  have las : ∀ y : Fin (B.R.N B.R.m - 1) → B.fields.E, iXc (I.rec7 l Z) y (Br.iL (N_m_succ B.R)) = 0 := fun y =>
    (hi y _).trans (dif_neg (lt_irrefl _))
  refine ⟨fun y => ext_vec (N_m_succ B.R) ?_ ?_, ext_vec (N_m_succ B.R) ?_ ?_⟩
  · refine ((l.per u I.mu0).gam_ini b g _).trans ?_
    exact (congrArg _ (ini _)).trans (ini _).symm
  · exact ((l.per u I.mu0).gam_last b g _).trans ((las _).trans (las _).symm)
  · refine ((l.per u I.mu0).gam_ini b g _).trans ?_
    have z : iniH (E := B.fields.E) (N_m_succ B.R) (TC.z0 X u) = 0 := by
      funext j
      exact if_neg (by have := j.2; show ¬ (j.1 + 1 = _); omega)
    exact (congrArg _ z).trans ((Matrix.mulVec_zero _).trans z.symm)
  · exact (l.per u I.mu0).gam_last b g _

theorem stabMap_tied : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ (A : ∀ u, Formalism.L2.Herm.AtT (I.rec7 l Z) u (H.vT u) (H.Fv u)), CarT H F A → Formalism.L2.Herm.SymmetricStabilizerMapCompatibility (I.rec7 l Z) H A := by
  intro B X I hOk hPins l Z H F hStd hCarH A hCarT u h1 c s
  have hF : ∀ u, I.StdF l Z u (F u) := fun u => (hStd u).1
  have hga := ga_eq_gam_mv I l Z H F hF u c
  have conj : ∀ v, ((I.stp u I.mu0 B.R.m).gam (I.perIn u I.mu0).b0 ((I.stp u I.mu0 B.R.m).mv (I.perIn u I.mu0).b0 ((I.perIn u I.mu0).tilPt c))).1 *ᵥ
      (((I.stp u I.mu0 B.R.m).gam _ (((I.rec7 l Z).fm u).stabMap c s).1).1 *ᵥ v) =
      ((I.stp u I.mu0 B.R.m).gam (I.perIn u I.mu0).b0 ((I.perIn u I.mu0).ext c.1 s.1)).1 *ᵥ
      (((I.stp u I.mu0 B.R.m).gam (I.perIn u I.mu0).b0 ((I.stp u I.mu0 B.R.m).mv (I.perIn u I.mu0).b0 ((I.perIn u I.mu0).tilPt c))).1 *ᵥ v) := by
    intro v
    show _ *ᵥ (((I.stp u I.mu0 B.R.m).gam (I.perIn u I.mu0).b0 (((I.stp u I.mu0 B.R.m).mv (I.perIn u I.mu0).b0 ((I.perIn u I.mu0).tilPt c))⁻¹ * (I.perIn u I.mu0).ext c.1 s.1 *
          (I.stp u I.mu0 B.R.m).mv (I.perIn u I.mu0).b0 ((I.perIn u I.mu0).tilPt c))).1 *ᵥ v) = _
    rw [map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    congr 1
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  have key : ∀ y, crdN (I.rec7 l Z) (I.rec7 l Z).R.m le_rfl (((A u).tilG c).1 (Formalism.L2.Herm.stabMLinS (I.rec7 l Z) H u h1 _
      (((I.rec7 l Z).fm u).stabMap c s) (((A u).tilG c).1.symm y))) =
      ((I.stp u I.mu0 B.R.m).gam (I.perIn u I.mu0).b0 ((I.perIn u I.mu0).ext c.1 s.1)).1 *ᵥ crdN (I.rec7 l Z) (I.rec7 l Z).R.m le_rfl y := by
    intro y
    have hw : ((F u).til.ga c).1.1 *ᵥ crdN (I.rec7 l Z) (I.rec7 l Z).R.m le_rfl (((A u).tilG c).1.symm y) =
        crdN (I.rec7 l Z) (I.rec7 l Z).R.m le_rfl y := by
      rw [← crdN_tilG I l Z H F A hCarT u c, LinearEquiv.apply_symm_apply]
    rw [crdN_tilG I l Z H F A hCarT u c, crdN_stabM I l Z H F hF hCarH u h1, ← hw, hga]
    exact conj _
  have hiX : ∀ x, crdN (I.rec7 l Z) (I.rec7 l Z).R.m le_rfl ((I.rec7 l Z).sp.iX' x) = iXc (I.rec7 l Z) (crdP (I.rec7 l Z) x) := by
    intro x
    simp [iXc, crdN, crdP]
  have hext := gam_ext I hOk hPins l Z u c.1 s.1
  refine ⟨fun x => ?_, ?_⟩
  · apply (crdN (I.rec7 l Z) (I.rec7 l Z).R.m le_rfl).injective
    rw [key, hiX, hiX, hext.1, crdP_stabP I l Z H F A hF hCarT u c s x]
    rfl
  · apply (crdN (I.rec7 l Z) (I.rec7 l Z).R.m le_rfl).injective
    rw [key, ← hCarT.z0 u]
    have hz : (F u).til.z0 = TC.z0 X u := funext fun j => (hF u).z0 j
    rw [hz, hext.2]

end GlobalTheory.Mem.Col2.HAt.Stab
