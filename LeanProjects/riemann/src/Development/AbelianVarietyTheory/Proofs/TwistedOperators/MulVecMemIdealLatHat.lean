import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.LevelGroupLifts
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GeneralDiagonalMatrix
import Formalism.LocalToGlobal.ProjectiveLattices.SpMapAlgHomId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPinnedOfIsUnf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformFamilyUnfoldingCompat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchingDeterminantRootOfUnity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTraceFormLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstMulReadingOfMovedSectionAtFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateCharacterOnLifts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformFamilyComponentIndex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedSectionReadingEqMovedFrameReadingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeBasisHermitianSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedLatticeStabilizerIffBasisIntegral
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.AbsGeneratorRatioEqOneOfUnitFrameMove
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ActLevFullLevelGroupFramedPoints
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueFramedPointMoveUniversalTriple
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointMoveCalculus
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryLatticeRationalTranslateInvariance
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CongruenceLatticeFractionalMultipleAgree

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UnitConst

section Free

open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GeoLevel GlobalTheory.LevelCusp
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

theorem isMatch_symm {X X' : Data E r} {a : GL (Fin r) E} (h : IsMatch X X' a) : IsMatch X' X a⁻¹ := by
  have e : ∀ v : Fin r → E, (a : Matrix (Fin r) (Fin r) E) *ᵥ (((a⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v) = v :=
    fun v => by rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  exact ⟨h.psi.symm, h.p0.symm, h.xi.symm, fun u v => by rw [← h.iso, e, e], fun v => by rw [h.lat, e]⟩

theorem isMatch_trans {X X' X'' : Data E r} {a b : GL (Fin r) E} (h : IsMatch X X' a) (h' : IsMatch X' X'' b) :
    IsMatch X X'' (b * a) :=
  ⟨h.psi.trans h'.psi, h.p0.trans h'.p0, h.xi.trans h'.xi,
    fun u v => by rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h'.iso, h.iso],
    fun v => by rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← h'.lat, h.lat]⟩

omit [NumberField E] [IsCMField E] in
theorem lact_cast_lact {Ψ Ψ' Ψ'' : Finset (E →+* ℂ)} (h : Ψ = Ψ') (h' : Ψ' = Ψ'') (a b : GL (Fin r) E) (x : Frame Ψ r) :
    lact b (castFr h' (lact a (castFr h x))) = lact (b * a) (castFr (h.trans h') x) := by
  subst h h'
  funext τ
  show (b : Matrix (Fin r) (Fin r) E).map τ.1 * ((a : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ) =
    ((b * a : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ
  rw [Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]

omit [NumberField E] [IsCMField E] in
theorem lact_one_cast {Ψ : Finset (E →+* ℂ)} (h : Ψ = Ψ) (x : Frame Ψ r) : lact 1 (castFr h x) = x := by
  funext τ
  show ((1 : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ = mat x τ
  rw [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]

variable {U : Formalism.L2.PjFree.Unf Xo c σ r} {ρ : Xo.X ⟶ Xo.X} {ν : SABMap Xo.univ.t Xo.univ.t ρ}

theorem comp_eq_of_moveMatch (hU : Formalism.L2.PjFree.IsUnf U) (hs : ρ ≫ Xo.s = Xo.s) {k k' k'' : U.Comp}
    {δ δ' : GL (Fin r) E} {h : IsMatch (U.X k) (U.X k') δ} {h' : IsMatch (U.X k) (U.X k'') δ'}
    (m : MoveMatch U U k k' h ρ ν) (m' : MoveMatch U U k k'' h' ρ ν) : k' = k'' := by
  obtain ⟨x, hx⟩ := (GlobalTheory.frames_isConnected E r (U.X k)).nonempty
  obtain ⟨y, hy⟩ := (GlobalTheory.exists_unique_frMove E H Dw l Xo c ρ ν hs _ (U.un k ⟨x, hx⟩)).1
  obtain ⟨a1, a2⟩ := m _ y hy
  obtain ⟨b1, b2⟩ := m' _ y hy
  obtain ⟨t, ht⟩ := exists_frBor_gen _ _ (b1.symm.trans a1) (b2.symm.trans a2)
  obtain ⟨_, -, _, -, e⟩ := (hU.2.2.2.1 _ _ _ _).1 ⟨_, ht⟩
  exact (congrArg Sigma.fst e).symm

def ExactAt (U : Formalism.L2.PjFree.Unf Xo c σ r) (k : U.Comp) : Prop :=
  ∀ (δ : GL (Fin r) E) (h : IsMatch (U.X k) (U.X k) δ) (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ),
    ρ ≫ Xo.s = Xo.s → MoveMatch U U k k h ρ ν → ∀ w n, Dom w n → ∀ f ∈ sec Xo c w n, ∀ f' ∈ sec Xo c w n,
      (∀ y y' : FrPt Xo c (CAt σ), FrMove ρ ν y y' → evR Xo c f' y = evR Xo c f y') → ∀ x ∈ (U.X k).dom,
        Formalism.L2.PjFree.rdU U f' k x = Formalism.L2.PjFree.rdU U f k (lact δ (castFr h.psi x))

theorem rdU_eq_of_moveMatch (hs : ρ ≫ Xo.s = Xo.s) {k k' : U.Comp} (hE : ExactAt U k')
    {δ δ' : GL (Fin r) E} {h : IsMatch (U.X k) (U.X k') δ} {h' : IsMatch (U.X k) (U.X k') δ'}
    (m : MoveMatch U U k k' h ρ ν) (m' : MoveMatch U U k k' h' ρ ν) {w : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hD : Dom w n)
    {f : Rul Xo c} (hf : f ∈ sec Xo c w n) {x : Frame (U.X k).Ψ r} (hx : x ∈ (U.X k).dom) :
    Formalism.L2.PjFree.rdU U f k' (lact δ (castFr h.psi x)) = Formalism.L2.PjFree.rdU U f k' (lact δ' (castFr h'.psi x)) := by
  obtain ⟨ν₀, -, h₀⟩ := (GlobalTheory.MoveCalc.frMove_calculus E H Dw l Xo c).1
  have u₀ : ∀ y y' : FrPt Xo c (CAt σ), FrMove (𝟙 Xo.X) ν₀ y y' → y' = y := fun y y' hy =>
    (GlobalTheory.exists_unique_frMove E H Dw l Xo c _ ν₀ (Category.id_comp _) _ y).2 _ _ ν₀ rfl hy (h₀ _ y)
  have h'' := isMatch_trans (isMatch_symm h) h'
  have mm : MoveMatch U U k' k' h'' (𝟙 Xo.X) ν₀ := by
    intro z y' hy'
    rw [u₀ _ _ hy']
    have hz := (isMatch_symm h).mem_dom z.2
    obtain ⟨y, hy⟩ := (GlobalTheory.exists_unique_frMove E H Dw l Xo c ρ ν hs _ (U.un k ⟨_, hz⟩)).1
    obtain ⟨a1, a2⟩ := m _ y hy
    obtain ⟨b1, b2⟩ := m' _ y hy
    have e1 : (⟨_, h.mem_dom hz⟩ : (U.X k').dom) = z := Subtype.ext (by
      show lact δ (castFr h.psi (lact δ⁻¹ (castFr (isMatch_symm h).psi z.1))) = z.1
      rw [lact_cast_lact, mul_inv_cancel, lact_one_cast])
    have e2 : (⟨_, h'.mem_dom hz⟩ : (U.X k').dom) = ⟨_, h''.mem_dom z.2⟩ := Subtype.ext (lact_cast_lact _ _ _ _ _)
    rw [e1] at a1 a2
    rw [e2] at b1 b2
    exact ⟨a1.symm.trans b1, a2.symm.trans b2⟩
  rw [hE _ h'' _ ν₀ (Category.id_comp _) mm w n hD f hf f hf (fun y y' hy => by rw [u₀ y y' hy]) _ (h.mem_dom hx),
    lact_cast_lact, inv_mul_cancel_right]

theorem exists_const (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U) (hE : ∀ k, ExactAt U k)
    (hs : ρ ≫ Xo.s = Xo.s) {k₀ k₀' : U.Comp} {δ₀ : GL (Fin r) E} {h₀ : IsMatch (U.X k₀) (U.X k₀') δ₀}
    (m₀ : MoveMatch U U k₀ k₀' h₀ ρ ν) (n : ℕ) :
    ∃ ε : ℂ, ‖ε‖ = 1 ∧ ∀ w, Dom w n → ∀ f ∈ sec Xo c w n, ∀ f' ∈ sec Xo c w n,
      (∀ y y' : FrPt Xo c (CAt σ), FrMove ρ ν y y' → evR Xo c f' y = evR Xo c f y') →
      ∀ (k k' : U.Comp) (δ : GL (Fin r) E) (h : IsMatch (U.X k) (U.X k') δ), k = k₀ → MoveMatch U U k k' h ρ ν →
      ∀ x ∈ (U.X k).dom, Formalism.L2.PjFree.rdU U f' k x = ε * Formalism.L2.PjFree.rdU U f k' (lact δ (castFr h.psi x)) := by
  obtain ⟨ε, hε, he⟩ := exists_const_rdU_of_moveMatch E H Dw l Xo c σ r U U hσ hU hU k₀ k₀' δ₀ h₀ ρ ν hs m₀
    (fun x y' t hx hm hb => cabs_gen_eq_one_of_move E H Dw l Xo c σ r U hσ hU ρ ν k₀ k₀' x _ y' t hm hb hx
      (fun τ i => (congrArg norm (h₀.dmin_eq x.1 τ i)).trans (hx _ i))) n
  refine ⟨ε, hε, fun w hD f hf f' hf' hv k k' δ h hk m x hx => ?_⟩
  subst hk
  obtain rfl := comp_eq_of_moveMatch hU hs m₀ m
  rw [he w hD f hf f' hf' hv x hx, rdU_eq_of_moveMatch hs (hE _) m₀ m hD hf hx]

theorem rdU_eq_of_comp_eq (hE : ∀ k, ExactAt U k) (hs : ρ ≫ Xo.s = Xo.s) {w : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hD : Dom w n)
    {f f' : Rul Xo c} (hf : f ∈ sec Xo c w n) (hf' : f' ∈ sec Xo c w n)
    (hv : ∀ y y' : FrPt Xo c (CAt σ), FrMove ρ ν y y' → evR Xo c f' y = evR Xo c f y')
    {k k' : U.Comp} {δ : GL (Fin r) E} {h : IsMatch (U.X k) (U.X k') δ} (hk : k' = k) (m : MoveMatch U U k k' h ρ ν)
    {x : Frame (U.X k).Ψ r} (hx : x ∈ (U.X k).dom) :
    Formalism.L2.PjFree.rdU U f' k x = Formalism.L2.PjFree.rdU U f k' (lact δ (castFr h.psi x)) := by
  subst hk
  exact hE _ δ h ρ ν hs m w n hD f hf f' hf' hv x hx

end Free

section Lifts

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.LevelGroupLifts
open GlobalTheory.Member (FinCong)
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D}

theorem halfVec_eq_smul (b : 𝓞 D.host.E) (z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    halfVec V b z = ((1 : Af D.host.F) ⊗ₜ[D.host.F] (b : D.host.E)) • z := rfl

theorem mulVec_halfVec (k : GA D V) (b : 𝓞 D.host.E) (z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    (finHom V k).1 *ᵥ halfVec V b z = halfVec V b ((finHom V k).1 *ᵥ z) := by
  rw [halfVec_eq_smul, halfVec_eq_smul, Matrix.mulVec_smul]

theorem finVec_smul (b : 𝓞 D.host.E) (v : Fin V.rank → D.host.E) : finVec V (b • v) = halfVec V b (finVec V v) := by
  funext i
  show (1 : Af D.host.F) ⊗ₜ[D.host.F] ((b : D.host.E) * v i) = _
  rw [halfVec, finVec, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem finVec_add (u v : Fin V.rank → D.host.E) : finVec V (u + v) = finVec V u + finVec V v := by
  funext i
  exact TensorProduct.tmul_add _ _ _

theorem halfVec_halfVec (a b : 𝓞 D.host.E) (z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    halfVec V a (halfVec V b z) = halfVec V (a * b) z := by
  rw [halfVec_eq_smul, halfVec_eq_smul, halfVec_eq_smul, smul_smul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rfl

theorem halfVec_natCast (n : ℕ) (z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    halfVec V (n : 𝓞 D.host.E) z = n • z := by
  rw [halfVec_eq_smul, ← Nat.cast_smul_eq_nsmul (Af D.host.F ⊗[D.host.F] D.host.E)]
  congr 1
  exact (congrArg _ (map_natCast (algebraMap (𝓞 D.host.E) D.host.E) n)).trans
    (map_natCast (Algebra.TensorProduct.includeRight (R := D.host.F) (A := Af D.host.F) (B := D.host.E)) n)

theorem halfVec_mem_latGHat (g : GA D V) (b : 𝓞 D.host.E) {z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E}
    (hz : z ∈ latGHat V g) : halfVec V b z ∈ latGHat V g := by
  rw [halfVec_eq_smul]
  induction hz using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, y, hy, rfl⟩ := hx
    refine AddSubgroup.subset_closure ⟨b • a, (D.host.AA : Submodule (𝓞 D.host.E) D.host.E).smul_mem b ha, y, hy, ?_⟩
    funext i
    show (1 ⊗ₜ (b : D.host.E)) * ((1 ⊗ₜ a) * y i) = (1 ⊗ₜ ((b : D.host.E) * a)) * y i
    rw [← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem finCong_of_gLat {k : GA D V}
    (h : gLat V k = (latHat V : Set (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E))) : FinCong V 1 k := fun z hz =>
  ⟨_, sub_mem (show (finHom V k).1 *ᵥ z ∈ (latHat V : Set _) from h ▸ ⟨z, hz, rfl⟩) hz, (one_smul _ _).symm⟩

theorem mulVec_mem_idealLatHat {k : GA D V} (h : FinCong V 1 k) {I : Ideal (𝓞 D.host.E)}
    {z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E} (hz : z ∈ idealLatHat V I) :
    (finHom V k).1 *ᵥ z ∈ idealLatHat V I := by
  induction hz using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, y, hy, rfl⟩ := hx
    exact AddSubgroup.subset_closure ⟨a, ha, _, (GlobalTheory.Member.AALev.congruences_agree D V k).1.2 h y hy, mulVec_halfVec k a y⟩
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.mulVec_neg]; exact neg_mem hx

theorem gLat_mul {k k' : GA D V}
    (h : gLat V k' = (latHat V : Set (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E))) : gLat V (k * k') = gLat V k := by
  conv_rhs => rw [gLat, ← h, gLat, Set.image_image]
  simp only [gLat, map_mul, Units.val_mul, Subgroup.coe_mul, Matrix.mulVec_mulVec]

theorem gLat_one : gLat V 1 = (latHat V : Set (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E)) := by
  simp [gLat]

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E}

section

variable {Dw : Datum H} {l : Level H} {ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)}
  {g g' : LaMod Dw l ≃ₗ[𝓞 D.host.E] LaMod Dw l} {k k' : GA D V}

theorem isLift_mul (h : IsLift V Dw l ι g k) (h' : IsLift V Dw l ι g' k') : IsLift V Dw l ι (g * g') (k * k') := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨h1', h2', h3'⟩ := h'
  refine ⟨mul_mem h1 h1', (gLat_mul h2').trans h2, fun a c hc => ?_⟩
  obtain ⟨b, hb⟩ := Submodule.Quotient.mk_surjective _ (g' (Submodule.Quotient.mk a))
  have := add_mem (mulVec_mem_idealLatHat (finCong_of_gLat h2) (h3' a b hb)) (h3 b c (by rw [hb]; exact hc))
  rw [Matrix.mulVec_sub, sub_add_sub_cancel, Matrix.mulVec_mulVec] at this
  rw [map_mul]
  exact this

theorem isLift_inv (h : IsLift V Dw l ι g k) : IsLift V Dw l ι g⁻¹ k⁻¹ := by
  obtain ⟨h1, h2, h3⟩ := h
  have h2' : gLat V k⁻¹ = (latHat V : Set (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E)) :=
    (gLat_mul (k := k⁻¹) h2).symm.trans (by rw [inv_mul_cancel]; exact gLat_one)
  refine ⟨inv_mem h1, h2', fun a b hb => ?_⟩
  have := neg_mem (mulVec_mem_idealLatHat (finCong_of_gLat h2') (h3 b a (by
    rw [hb]; exact (g.apply_symm_apply _).symm)))
  have e : (finHom V k⁻¹).1 * (finHom V k).1 = 1 := by
    have := congrArg Units.val ((map_mul (finHom V) k⁻¹ k).symm.trans
      (by rw [inv_mul_cancel, map_one] : finHom V (k⁻¹ * k) = 1))
    exact this
  rwa [Matrix.mulVec_sub, neg_sub, Matrix.mulVec_mulVec, e, Matrix.one_mulVec] at this

def liftGrp (h : IsLift V Dw l ι g k) : Subgroup ((LaMod Dw l ≃ₗ[𝓞 D.host.E] LaMod Dw l) × GA D V) where
  carrier := {p | IsLift V Dw l ι p.1 p.2}
  one_mem' := by
    have := isLift_mul h (isLift_inv h)
    rwa [mul_inv_cancel, mul_inv_cancel] at this
  mul_mem' := isLift_mul
  inv_mem' := isLift_inv

end

theorem halfVec_add (b : 𝓞 D.host.E) (x y : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    halfVec V b (x + y) = halfVec V b x + halfVec V b y := funext fun _ => mul_add _ _ _

theorem halfVec_neg (b : 𝓞 D.host.E) (x : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    halfVec V b (-x) = -halfVec V b x := funext fun _ => mul_neg _ _

theorem halfVec_sub (b : 𝓞 D.host.E) (x y : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    halfVec V b (x - y) = halfVec V b x - halfVec V b y := funext fun _ => mul_sub _ _ _

theorem halfVec_zero (b : 𝓞 D.host.E) : halfVec V b 0 = 0 := funext fun _ => mul_zero _

set_option maxHeartbeats 800000 in

theorem agrees_of_isLift {Dw : Datum H} {l : Level H} {ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)}
    {g : LaMod Dw l ≃ₗ[𝓞 D.host.E] LaMod Dw l} {k : GA D V} (h : IsLift V Dw l ι g k) :
    ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La), ∃ w ∈ latGHat V 1,
      (finHom V k).1.mulVec (finVec V (ι a)) - finVec V (ι (liftLa g a)) = (l.M : ℕ) • w := by
  have key : ∀ m ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E), ∀ z ∈ idealLatHat V l.Mb,
      ∃ w ∈ latGHat V 1, halfVec V m z = l.M • w := fun m hm z hz => by
    induction hz using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨b, hb, y, hy, rfl⟩ := hx
      obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 (l.prod ▸ Ideal.mul_mem_mul hb hm)
      exact ⟨_, halfVec_mem_latGHat 1 s hy, by
        rw [halfVec_halfVec, mul_comm, ← hs, mul_comm, ← halfVec_halfVec, halfVec_natCast]⟩
    | zero => exact ⟨0, zero_mem _, by rw [halfVec_zero, nsmul_zero]⟩
    | add x y _ _ hx hy =>
      obtain ⟨w, hw, e⟩ := hx
      obtain ⟨w', hw', e'⟩ := hy
      exact ⟨w + w', add_mem hw hw', by rw [nsmul_add, ← e, ← e', halfVec_add]⟩
    | neg x _ hx =>
      obtain ⟨w, hw, e⟩ := hx
      exact ⟨-w, neg_mem hw, by rw [neg_nsmul, ← e, halfVec_neg]⟩
  intro a ha
  refine Submodule.smul_induction_on ha (fun m hm x _ => ?_) fun x y hx hy => ?_
  · obtain ⟨w, hw, e⟩ := key m hm _ (h.2.2 x _ (liftLa_spec g x))
    refine ⟨w, hw, ?_⟩
    rw [map_smul, map_smul, map_smul, finVec_smul, finVec_smul, mulVec_halfVec, ← e, halfVec_sub]
  · obtain ⟨w, hw, e⟩ := hx
    obtain ⟨w', hw', e'⟩ := hy
    refine ⟨w + w', add_mem hw hw', ?_⟩
    rw [map_add, map_add, map_add, finVec_add, finVec_add, Matrix.mulVec_add, nsmul_add, ← e, ← e',
      add_sub_add_comm]

end Lifts

section Main

open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.LevelGroupLifts GlobalTheory.GeoLevel GlobalTheory.LevelCusp
open GlobalTheory.Dict (castFr)
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {T : CoreJ D} {j : ℕ} {σ : T.Q.c.F →+* ℂ}

theorem one_le_rank (h : LawsJ T) (hj : InR D j) : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by
  have hp := h.pins
  rw [(hp.2.2.2 j hj).1, (hp.2.2.2 j hj).2.1]
  have := hj.1; have := hj.2; have := D.R.m_add_three_le_k
  simp only [Ranks.sigW]; omega

set_option maxHeartbeats 1000000 in

theorem exists_move (h : LawsJ T) (hj : InR D j) (hσ : GoodEmb T.Q.c σ) (hr : (T.V j σ).rank = D.R.r) {g : LevGrp T j}
    {k : GA D (T.V j σ)} (hk : IsLift (T.V j σ) (T.Q.Dw j) T.Q.l (iotaAt T j σ hr) g k) :
    ∃ (ρ : (T.Q.Xo j).X ⟶ (T.Q.Xo j).X) (ν : SABMap (T.Q.Xo j).univ.t (T.Q.Xo j).univ.t ρ),
      ρ ≫ (T.Q.Xo j).s = (T.Q.Xo j).s ∧
      (∀ a n, ∀ f ∈ sec (T.Q.Xo j) T.Q.c a n, ∀ y y' : FrPt (T.Q.Xo j) T.Q.c (CAt σ), FrMove ρ ν y y' →
        evR (T.Q.Xo j) T.Q.c (actLev (Xo := T.Q.Xo j) T.Q.c (GlobalTheory.FormTies.levFull (T.Q.Dw j) T.Q.l) g f) y =
          evR (T.Q.Xo j) T.Q.c f y') ∧
      ∀ x : GA D (T.V j σ), ∃ (δ : GL (Fin D.R.r) D.host.E)
        (hm : IsMatch ((T.U j σ).X (T.dict j σ x).1) ((T.U j σ).X (T.dict j σ (x * k)).1) δ),
        (T.dict j σ (x * k)).2 = lact δ (castFr hm.psi (T.dict j σ x).2) ∧
          MoveMatch (Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) (Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) (T.dict j σ x).1
            (T.dict j σ (x * k)).1 hm ρ ν := by
  have hA : T.Q.l.A = 1 := h.pins.2.1.2
  have hL := GlobalTheory.FullLevelAction.actLev_levFull D T.Q j (one_le_rank h hj) hA
  obtain ⟨_, ρ, ν, hiso, hmv, -⟩ := hL.total g (CAt σ) (GlobalTheory.IndefiniteRowSideFullHecke.GeneralDiagonalMatrix.ptOf T h j hj σ hσ 1)
  refine ⟨ρ, ν, hmv.1, fun a n f hf y y' hy => ?_, fun x => ?_⟩
  · have h1 := mvPt_spec hL.total g y
    have h2 : levActR (GlobalTheory.FormTies.levFull (T.Q.Dw j) T.Q.l) g y y' := ⟨ρ, ν, hiso, hmv, hy⟩
    exact (evalAt_actL hL (h.evalWD j hj) frMap_trans_id g hf.1 y).trans
      (evalAt_congr_id (h.evalWD j hj) frMap_trans_id hf.1 (hL.func g _ y _ _ h1 h2) (hL.func g _ y _ _ h2 h1))
  · obtain ⟨hr', m, e, F, ik, φ, th, -, -, hth, hd⟩ := h.adPin j hj σ hσ
    obtain ⟨_, hW⟩ := h.modelW j hj σ hσ
    obtain ⟨δ, hm, h1, h2⟩ := dict_mul_markRel D _ _ _ _ _ σ (T.V j σ) _ hr (T.U j σ) (T.dict j σ) (iotaAt T j σ hr) m e F
      ik φ th (T.x₀ j σ) (h.unf j hj σ hσ) hW hth hd k (liftLa g) hk.1 (finCong_of_gLat hk.2.1) (agrees_of_isLift hk) x
    exact ⟨δ, hm, h1, moveMatch_of_markRel _ _ _ _ _ _ σ _ (Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) m e F ik φ hσ (one_le_rank h hj) hA
      hd.1 _ _ δ hm (liftLa g) ρ ν h2 hmv⟩

section

variable {g : LevGrp T j} {k : GA D (T.V j σ)} {hr : (T.V j σ).rank = D.R.r} {a : (D.host.E →+* ℂ) × ℕ → ℕ} {n : ℕ}
  {ρ : LevGrp T j →* (T.cuspA j a n →ₗ[T.Q.c.F] T.cuspA j a n)}

variable (T σ) in

def rdAt (f : T.cuspA j a n) (x : GA D (T.V j σ)) : ℂ :=
  rdU (T.U j σ) (f : T.R j) (T.dict j σ x).1 (T.dict j σ x).2

end

end Main

end GlobalTheory.UnitConst
