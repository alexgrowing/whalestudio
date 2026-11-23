import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsArchEquivEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisAdaptedToCartanInvolution

noncomputable section

namespace GlobalTheory.Doubling

open scoped TensorProduct Matrix ComplexOrder
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.AdelicU Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open Formalism.IndefR.Datum (IsCartanInv InfFam compAt)
open Formalism.MainNotions.StandardLattice (infMat)

section Complex

variable {n : ℕ} {G b c d : Matrix (Fin n) (Fin n) ℂ}

theorem diagonal_sign_mul_self (ε : Fin n → Bool) :
    (Matrix.diagonal fun i => if ε i then (1 : ℂ) else -1) * (Matrix.diagonal fun i => if ε i then 1 else -1) = 1 := by
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  split_ifs <;> simp

theorem diagonal_sign_conjTranspose (ε : Fin n → Bool) :
    (Matrix.diagonal fun i => if ε i then (1 : ℂ) else -1)ᴴ = Matrix.diagonal fun i => if ε i then 1 else -1 := by
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  simp only [Pi.star_apply]
  split_ifs <;> simp

theorem mul_conjTranspose_mul_eq (hbc : b * c = 1) (h : bᴴ * G * b = d) : b * bᴴ * G = b * d * c := by
  rw [← h]
  calc b * bᴴ * G = b * bᴴ * G * (b * c) := by rw [hbc, mul_one]
    _ = _ := by simp only [mul_assoc]

theorem isCartanInv_of_frame (hbc : b * c = 1) (h : bᴴ * G * b = d) (hd : d * d = 1) (hd' : dᴴ = d) :
    IsCartanInv G (b * bᴴ * G) := by
  have hcb : c * b = 1 := mul_eq_one_comm.1 hbc
  have h1 : bᴴ * cᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hcb, Matrix.conjTranspose_one]
  have h2 : cᴴ * bᴴ = 1 := mul_eq_one_comm.1 h1
  have hG : G = cᴴ * d * c := by
    rw [← h]
    calc G = (cᴴ * bᴴ) * G * (b * c) := by rw [h2, hbc, one_mul, mul_one]
      _ = _ := by simp only [mul_assoc]
  have hs : G * (b * d * c) = cᴴ * 1 * c := by
    rw [hG]
    calc cᴴ * d * c * (b * d * c) = cᴴ * (d * (c * b) * d) * c := by simp only [mul_assoc]
      _ = _ := by rw [hcb, mul_one, hd]
  rw [mul_conjTranspose_mul_eq hbc h]
  refine ⟨?_, ?_, ?_⟩
  · calc b * d * c * (b * d * c) = b * (d * (c * b) * d) * c := by simp only [mul_assoc]
      _ = 1 := by rw [hcb, mul_one, hd, mul_one, hbc]
  · rw [mul_assoc _ G, hs, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hd', hG]
    calc cᴴ * (d * bᴴ) * (cᴴ * 1 * c) = cᴴ * d * (bᴴ * cᴴ) * c := by simp only [mul_assoc, one_mul]
      _ = _ := by rw [h1, mul_one]
  · rw [hs]
    exact Matrix.PosDef.one.conjTranspose_mul_mul_same
      (Matrix.mulVec_injective_of_isUnit (IsUnit.of_mul_eq_one _ hcb))

theorem unitary_iff_commute (hbc : b * c = 1) (h : bᴴ * G * b = d) (hd : d * d = 1)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : gᴴ * G * g = G) :
    (c * g * b)ᴴ * (c * g * b) = 1 ↔ Commute g (b * bᴴ * G) := by
  have hcb : c * b = 1 := mul_eq_one_comm.1 hbc
  have h1 : bᴴ * cᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hcb, Matrix.conjTranspose_one]
  have h2 : cᴴ * bᴴ = 1 := mul_eq_one_comm.1 h1
  set u := c * g * b with hu
  have hud : uᴴ * d * u = d := by
    rw [hu, ← h, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
    calc bᴴ * (gᴴ * cᴴ) * (bᴴ * G * b) * (c * g * b) = bᴴ * (gᴴ * (cᴴ * bᴴ) * G * (b * c) * g) * b := by
          simp only [mul_assoc]
      _ = _ := by rw [h2, hbc, mul_one, mul_one, hg]
  have hgu : g = b * u * c := by
    calc g = (b * c) * g * (b * c) := by rw [hbc, one_mul, mul_one]
      _ = _ := by simp only [hu, mul_assoc]
  have e1 : g * (b * d * c) = b * (u * d) * c := by
    rw [hgu]
    calc b * u * c * (b * d * c) = b * (u * (c * b) * d) * c := by simp only [mul_assoc]
      _ = _ := by rw [hcb, mul_one]
  have e2 : (b * d * c) * g = b * (d * u) * c := by
    rw [hgu]
    calc b * d * c * (b * u * c) = b * (d * (c * b) * u) * c := by simp only [mul_assoc]
      _ = _ := by rw [hcb, mul_one]
  have e3 : ∀ x, c * (b * x * c) * b = x := fun x => by
    calc c * (b * x * c) * b = (c * b) * x * (c * b) := by simp only [mul_assoc]
      _ = x := by rw [hcb, one_mul, mul_one]
  rw [mul_conjTranspose_mul_eq hbc h, Commute, SemiconjBy, e1, e2]
  constructor
  · intro hU
    have hU' : u * uᴴ = 1 := mul_eq_one_comm.1 hU
    congr 2
    calc u * d = u * (uᴴ * d * u) := by rw [hud]
      _ = (u * uᴴ) * d * u := by simp only [mul_assoc]
      _ = _ := by rw [hU', one_mul]
  · intro hc
    have h3 : u * d = d * u := by rw [← e3 (u * d), hc, e3]
    calc uᴴ * u = uᴴ * (u * d) * d := by rw [mul_assoc, mul_assoc, hd, mul_one]
      _ = 1 := by rw [h3, ← mul_assoc, hud, hd]

theorem exists_frame_of_isCartanInv {s : Matrix (Fin n) (Fin n) ℂ} (hs : IsCartanInv G s) :
    ∃ (b : GL (Fin n) ℂ) (ε : Fin n → Bool),
      b.1ᴴ * G * b.1 = Matrix.diagonal (fun i => if ε i then 1 else -1) ∧ b.1 * b.1ᴴ * G = s := by
  obtain ⟨p, q, B, B', h1, h2, h3, h4⟩ := GlobalTheory.exists_basis_adapted_to_cartan_involution n G s hs.1 hs.2.1 hs.2.2
  have hc : Fintype.card (Fin n) = Fintype.card (Fin p ⊕ Fin q) := by
    have := Matrix.trace_mul_comm B B'
    rw [h1, h2, Matrix.trace_one, Matrix.trace_one] at this
    exact_mod_cast this
  let e := Fintype.equivOfCardEq hc
  have k1 : B.submatrix id e * B'.submatrix e id = 1 := by
    rw [Matrix.submatrix_mul_equiv, h1, Matrix.submatrix_id_id]
  have k3 : (B.submatrix id e)ᴴ * G * B.submatrix id e = (Bᴴ * G * B).submatrix e e := by
    ext i j
    simp [Matrix.mul_apply]
  refine ⟨⟨_, _, k1, mul_eq_one_comm.1 k1⟩, fun i => (e i).isLeft, ?_, ?_⟩
  · change (B.submatrix id e)ᴴ * G * B.submatrix id e = _
    rw [k3, h3, ← Matrix.diagonal_one, ← Matrix.diagonal_one, Matrix.diagonal_neg, Matrix.fromBlocks_diagonal,
      Matrix.submatrix_diagonal_equiv]
    congr 1
    funext i
    have : ∀ x : Fin p ⊕ Fin q, Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1) x = if x.isLeft then 1 else -1 := by
      rintro (j | j) <;> simp
    exact this _
  · change B.submatrix id e * (B.submatrix id e)ᴴ * G = s
    rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]
    calc B * Bᴴ * G = B * Bᴴ * G * (B * B') := by rw [h1, mul_one]
      _ = B * (Bᴴ * G * B) * B' := by simp only [Matrix.mul_assoc]
      _ = s * B * B' := by rw [h3, h4]; rfl
      _ = s := by rw [Matrix.mul_assoc, h1, mul_one]

end Complex

section Place

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {w : InfinitePlace F}

theorem map_val_mul_inv {A : Type} [CommRing A] (f : A →+* ℂ) (a : GL (Fin n) A) :
    a.1.map f * (a⁻¹).1.map f = 1 := by
  rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]

omit [NumberField E] in
theorem infProj_fst (τ : EmbOver E w) (y : AF F ⊗[F] E) :
    infProj τ (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) y) = infEmb τ (compInf F E w y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y => rfl

theorem frame_local_iff (h : IsCMExt F E σ) (τ : EmbOver E w) (J : Matrix (Fin n) (Fin n) E)
    (c : Matrix (Fin n) (Fin n) (w.Completion ⊗[F] E)) (ε : Fin n → Bool) :
    cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ) c * JR w.Completion J * c = (Matrix.diagonal fun i => if ε i then 1 else -1) ↔
      (c.map (infEmb τ))ᴴ * J.map τ.1 * c.map (infEmb τ) = Matrix.diagonal fun i => if ε i then 1 else -1 := by
  have h2 : (JR w.Completion J).map (infEmb τ) = J.map τ.1 := by ext r s; simp [JR, inclR]
  rw [← (Matrix.map_injective (infEmb_bijective h τ).1).eq_iff]
  beta_reduce
  rw [Matrix.map_mul, Matrix.map_mul, Frames.map_cT_sigR h, h2, Matrix.diagonal_map (map_zero _)]
  refine iff_of_eq (congrArg₂ _ rfl (congrArg _ (funext fun i => ?_)))
  split_ifs <;> simp

omit [NumberField E] in
theorem map_conj_proj (τ : EmbOver E w) (J : Matrix (Fin n) (Fin n) E) (a : GL (Fin n) (AF F ⊗[F] E)) (g : GAd σ J) :
    ((bc (compInf F E w) a)⁻¹ * AdelicU.matHom _ σ J (projArch σ J w g) * bc (compInf F E w) a).1.map (infEmb τ) =
      ((a⁻¹).1.map (compInf F E w)).map (infEmb τ) * infMat σ J (infProj τ) g *
        (a.1.map (compInf F E w)).map (infEmb τ) := by
  have : infMat σ J (infProj τ) g = (AdelicU.matHom _ σ J (projArch σ J w g)).1.map (infEmb τ) :=
    Matrix.ext fun i j => infProj_fst τ _
  rw [this, Units.val_mul, Units.val_mul, Matrix.map_mul, Matrix.map_mul]
  rfl

theorem mem_stabArch_iff_unitary (h : IsCMExt F E σ) (τ : EmbOver E w) (J : Matrix (Fin n) (Fin n) E)
    (a : GL (Fin n) (AF F ⊗[F] E)) (g : GAd σ J) :
    projArch σ J w g ∈ stabArch σ J w (bc (compInf F E w) a) ↔
      (((a⁻¹).1.map (compInf F E w)).map (infEmb τ) * infMat σ J (infProj τ) g *
        (a.1.map (compInf F E w)).map (infEmb τ))ᴴ *
      (((a⁻¹).1.map (compInf F E w)).map (infEmb τ) * infMat σ J (infProj τ) g *
        (a.1.map (compInf F E w)).map (infEmb τ)) = 1 := by
  rw [mem_stabArch, ← map_conj_proj]
  generalize (bc (compInf F E w) a)⁻¹ * AdelicU.matHom _ σ J (projArch σ J w g) * bc (compInf F E w) a = x
  change cT _ x.1 * 1 * x.1 = 1 ↔ _
  rw [← (Matrix.map_injective (infEmb_bijective h τ).1).eq_iff]
  beta_reduce
  rw [mul_one, Matrix.map_mul, Frames.map_cT_sigR h, Matrix.map_one _ (map_zero _) (map_one _)]

end Place

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def frameInv (θ : InfFam D) (V : HSp D) (a : GL (Fin V.rank) (AE D)) (τ : D.what₂.Tau) :
    Matrix (Fin V.rank) (Fin V.rank) ℂ :=
  compAt θ τ a.1 * (compAt θ τ a.1)ᴴ * gramAt D V τ

variable {θ : InfFam D}

theorem compAt_eq_map (hθ : IsInfFam θ) (τ : D.what₂.Tau) {m n : ℕ} (y : Matrix (Fin m) (Fin n) (AE D)) :
    compAt θ τ y = (y.map (compInf _ _ (placeOf D τ))).map (infEmb (embOverOf D τ)) := by
  ext i j
  change θ τ (infPart D (y i j)) = infEmb (embOverOf D τ) (compInf _ _ (placeOf D τ) (y i j))
  rw [eq_infProj hθ (embOverOf D τ) rfl]
  exact infProj_fst _ _

theorem compAt_mul_inv (τ : D.what₂.Tau) {m : ℕ} (a : GL (Fin m) (AE D)) :
    compAt θ τ a.1 * compAt θ τ (a⁻¹).1 = 1 := map_val_mul_inv ((θ τ).comp (infPart D)) a

variable {V : HSp D} {a : GL (Fin V.rank) (AE D)}

theorem isMaj_iff (hθ : IsInfFam θ) : IsMaj V a ↔ ∀ τ, ∃ ε : Fin V.rank → Bool,
    (compAt θ τ a.1)ᴴ * gramAt D V τ * compAt θ τ a.1 = Matrix.diagonal fun i => if ε i then 1 else -1 := by
  refine (placeOf_bijective D).2.forall.trans (forall_congr' fun τ => exists_congr fun ε => ?_)
  rw [compAt_eq_map hθ]
  exact frame_local_iff (isCMExt_host D) (embOverOf D τ) V.gram _ ε

theorem IsMaj.isCartanInv (h : IsMaj V a) (hθ : IsInfFam θ) (τ : D.what₂.Tau) :
    IsCartanInv (gramAt D V τ) (frameInv θ V a τ) := by
  obtain ⟨ε, hε⟩ := (isMaj_iff hθ).1 h τ
  exact isCartanInv_of_frame (compAt_mul_inv τ a) hε (diagonal_sign_mul_self ε) (diagonal_sign_conjTranspose ε)

theorem infMat_isometry (hθ : IsInfFam θ) (τ : D.what₂.Tau) (g : GA D V) :
    (infMat D.sp.cm.sig V.gram (θ τ) g)ᴴ * gramAt D V τ * infMat D.sp.cm.sig V.gram (θ τ) g = gramAt D V τ := by
  rw [eq_infProj hθ (embOverOf D τ) rfl, infMat_infProj V.gram (isCMExt_host D)]
  exact (archEquiv V.gram (isCMExt_host D) (embOverOf D τ) (projArch _ _ _ g)).2

theorem IsMaj.mem_stabArch_iff (h : IsMaj V a) (hθ : IsInfFam θ) (τ : D.what₂.Tau) (g : GA D V) :
    projArch D.sp.cm.sig V.gram (placeOf D τ) g ∈
        stabArch D.sp.cm.sig V.gram (placeOf D τ) (bc (compInf _ _ (placeOf D τ)) a) ↔
      Commute (infMat D.sp.cm.sig V.gram (θ τ) g) (frameInv θ V a τ) := by
  obtain ⟨ε, hε⟩ := (isMaj_iff hθ).1 h τ
  refine Iff.trans ?_ (unitary_iff_commute (compAt_mul_inv τ a) hε (diagonal_sign_mul_self ε) (infMat_isometry hθ τ g))
  rw [compAt_eq_map hθ, compAt_eq_map hθ, eq_infProj hθ (embOverOf D τ) rfl]
  exact mem_stabArch_iff_unitary (isCMExt_host D) (embOverOf D τ) V.gram a g

theorem IsMaj.mem_Kmax_iff (h : IsMaj V a) (hθ : IsInfFam θ) (g : GA D V) : g ∈ Kmax V a ↔
    g ∈ levelOpen D.sp.cm.sig V.gram (frameLat V) ∧
      ∀ τ, Commute (infMat D.sp.cm.sig V.gram (θ τ) g) (frameInv θ V a τ) := by
  refine (mem_levelAll (σ := D.sp.cm.sig) (J := V.gram) (L := frameLat V) (a := a) (g := g)).trans ?_
  refine and_congr (mem_levelOpen (σ := D.sp.cm.sig) (J := V.gram) (L := frameLat V) (g := g)).symm ?_
  exact (placeOf_bijective D).2.forall.trans (forall_congr' fun τ => h.mem_stabArch_iff hθ τ g)

theorem exists_isMaj_frameInv_eq (hθ : IsInfFam θ) {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hs : ∀ τ, IsCartanInv (gramAt D V τ) (s τ)) :
    ∃ a, IsMaj V a ∧ IsLatticeFrame (frameLat V) a ∧ ∀ τ, frameInv θ V a τ = s τ := by
  choose b ε h1 h2 using fun τ => exists_frame_of_isCartanInv (hs τ)
  let e := fun τ => RingEquiv.ofBijective _ (infEmb_bijective (isCMExt_host D) (embOverOf D τ))
  let p := Equiv.ofBijective _ (placeOf_bijective D)
  let P := fun w : InfinitePlace D.host.F => GL (Fin V.rank) (w.Completion ⊗[D.host.F] D.host.E)
  let c : ∀ τ, P (p τ) := fun τ => bc (e τ).symm.toRingHom (b τ)
  obtain ⟨a, ha, hw⟩ := Frames.exists_isLatticeFrame_of_arch (frameLat V) (Equiv.piCongrLeft P p c)
  have hb : ∀ τ, compAt θ τ a.1 = (b τ).1 := fun τ => by
    have := hw (p τ)
    rw [Equiv.piCongrLeft_apply_apply] at this
    rw [compAt_eq_map hθ]
    refine (congrArg (fun x : P (p τ) => x.1.map (infEmb (embOverOf D τ))) this).trans ?_
    exact Matrix.ext fun i j => (e τ).apply_symm_apply _
  refine ⟨a, (isMaj_iff hθ).2 fun τ => ⟨ε τ, ?_⟩, ha, fun τ => ?_⟩
  · rw [hb, h1]
  · rw [frameInv, hb, h2]

theorem gramAt_dblSp (V : HSp D) (τ : D.what₂.Tau) :
    gramAt D (dblSp V) τ = blkMat finSumFinEquiv (gramAt D V τ) (-gramAt D V τ) :=
  (congrArg (fun x => x.map (tauE D τ)) (gram_hdbl V)).trans ((blkMat_map _ _ (map_zero _) _ _).trans
    (congrArg _ (Matrix.map_neg _ (map_neg (tauE D τ)) _)))

theorem frameInv_dblSp (θ : InfFam D) (V : HSp D) (a : GL (Fin V.rank) (AE D)) (τ : D.what₂.Tau) :
    frameInv θ (dblSp V) (blkGL finSumFinEquiv (a, a)) τ =
      blkMat finSumFinEquiv (frameInv θ V a τ) (-frameInv θ V a τ) := by
  have e : compAt θ τ (blkGL finSumFinEquiv (a, a)).1 = blkMat finSumFinEquiv (compAt θ τ a.1) (compAt θ τ a.1) :=
    blkMat_map finSumFinEquiv ((θ τ).comp (infPart D)) (map_zero _) _ _
  have e' : ∀ b : Matrix (Fin V.rank) (Fin V.rank) ℂ,
      (blkMat finSumFinEquiv b b)ᴴ = blkMat finSumFinEquiv bᴴ bᴴ := fun b => by
    simp [blkMat, Matrix.fromBlocks_conjTranspose]
  have : compAt θ τ (blkGL finSumFinEquiv (a, a)).1 * (compAt θ τ (blkGL finSumFinEquiv (a, a)).1)ᴴ *
      blkMat finSumFinEquiv (gramAt D V τ) (-gramAt D V τ) =
      blkMat finSumFinEquiv (frameInv θ V a τ) (-frameInv θ V a τ) := by
    rw [e, e', blkMat_mul, blkMat_mul, Matrix.mul_neg, frameInv]
  rw [frameInv, gramAt_dblSp]
  exact this

end GlobalTheory.Doubling

end
