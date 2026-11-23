import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.WchartLePreimage
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.RosatiAdj

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.DVR.QForm

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing

attribute [local instance] Over.cartesianMonoidalCategory

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
  (D : DegData V (maximalIdeal V))

include hϖ in

theorem exists_QVal (χ : D.toPre.X) : ∃ n : ℤ, QVal D.toPre ϖ χ n :=
  exists_genHasVal hϖ D.toPre.P.L D.toPre.P.isLB _ _ _ _ (D.toPre.psi χ) (D.toPre.psi_gen χ)

include hϖ in

theorem QVal_unique {χ : D.toPre.X} {n m : ℤ} (hn : QVal D.toPre ϖ χ n) (hm : QVal D.toPre ϖ χ m) : n = m :=
  genHasVal_unique hϖ D.toPre.P.L D.toPre.P.isLB _ _ _ _ _ hn hm

variable {Q : D.toPre.X → ℤ}

macro "secTac" : tactic => `(tactic| (simp [Sum.forall, Fin.forall_fin_succ, Over.w, Over.w_assoc, eSec, Matrix.cons_val_zero, Matrix.cons_val_succ]))

instance (P : PolAV (Spec (CommRingCat.of V))) : IsSeparated P.A.hom := by
  have : IsProper P.A.hom := P.isAb.proper
  infer_instance

lemma over_sec {Y B : Over (Spec (CommRingCat.of V))} (q : 𝟙_ (Over (Spec (CommRingCat.of V))) ⟶ Y) (f : Y ⟶ B) :
    (q.left ≫ f.left) ≫ B.hom = 𝟙 _ := by
  rw [Category.assoc, Over.w f]
  first
  | simpa using Over.w q
  | exact Over.w q

lemma rosatiφ_over {S : Scheme.{0}} (A : Over S) [GrpObj A] (f g : A ⟶ A) (k : Fin 6) :
    ∃ q : A ⊗ A ⟶ A, rosatiφ A f g k = q.left := by
  fin_cases k <;> first
  | exact ⟨_, rfl⟩
  | (simp [rosatiφ]; exact ⟨_, rfl⟩)

lemma sumElim_sec {Y : Scheme.{0}} {Ix Ix' : Type} {f : Ix → (Spec (CommRingCat.of V) ⟶ Y)}
    {g : Ix' → (Spec (CommRingCat.of V) ⟶ Y)} {s : Y ⟶ Spec (CommRingCat.of V)}
    (hf : ∀ k, f k ≫ s = 𝟙 _) (hg : ∀ k, g k ≫ s = 𝟙 _) : ∀ k, Sum.elim f g k ≫ s = 𝟙 _ := by
  rintro (k | k) <;> simp [hf, hg]

theorem rigK_val : GenHasVal ϖ D.toPre.P.L (fun _ : PUnit => 𝟙 _ ≫ eSec D.toPre.P.A)
    (fun _ => (toUnit (TK V)).left ≫ eSec D.toPre.P.A) (fun _ => by rw [Category.id_comp]; rfl) (fun _ => 1)
    D.toPre.rigK 0 :=
  genHasVal_pullGen_of (ϖ := ϖ) D.toPre.P.L _ _ D.toPre.rig D.toPre.rig_gen (𝟙 _) (toUnit (TK V)).left
    (by rw [Category.comp_id]; rfl)

include hϖ in

theorem tau_val (hQ : IsQ D.toPre ϖ Q) (a b : D.toPre.X) :
    ∃ (φ : _) (hφ : _), (∀ k, φ k ≫ D.toPre.P.A.hom = 𝟙 _) ∧
      GenHasVal ϖ D.toPre.P.L φ _ hφ _ (D.toPre.tau a b) (bOf D.toPre Q a b) := by
  have hL := D.toPre.P.isLB
  have h1 := genHasVal_mulGen hϖ D.toPre.P.L hL _ _ _ _ _ _ _ _ _ _ (hQ (a + b))
    (genHasVal_invGen D.toPre.P.L hL _ _ _ _ _ (hQ a))
  have h2 := genHasVal_mulGen hϖ D.toPre.P.L hL _ _ _ _ _ _ _ _ _ _ h1
    (genHasVal_invGen D.toPre.P.L hL _ _ _ _ _ (hQ b))
  have h3 := genHasVal_mulGen hϖ D.toPre.P.L hL _ _ _ _ _ _ _ _ _ _ h2
    (genHasVal_invGen D.toPre.P.L hL _ _ _ _ _ (rigK_val D))
  have h4 : Q (a + b) + -Q a + -Q b + -0 = bOf D.toPre Q a b := by simp only [bOf]; ring
  rw [h4] at h3
  exact ⟨_, _, by secTac, h3⟩

include hϖ in

theorem bOf_add_left (hQ : IsQ D.toPre ϖ Q) (a a' b : D.toPre.X) :
    bOf D.toPre Q (a + a') b = bOf D.toPre Q a b + bOf D.toPre Q a' b := by
  have hL := D.toPre.P.isLB
  obtain ⟨_, _, hsA, hA⟩ := tau_val hϖ D hQ (a + a') b
  obtain ⟨_, _, hsB, hB⟩ := tau_val hϖ D hQ a b
  obtain ⟨_, _, hsC, hC⟩ := tau_val hϖ D hQ a' b
  have hcub := genHasVal_pullGen_of (ϖ := ϖ) D.toPre.P.L _ _ D.toPre.cub.t D.toPre.cub.isGen
    (lift (D.toPre.c a) (lift (D.toPre.c a') (D.toPre.c b))).left (D.toPre.pt3 a a' b)
    (by simp [DegPre.pt3, ← CartesianMonoidalCategory.comp_lift])
  have h1 := genHasVal_mulGen hϖ D.toPre.P.L hL _ _ _ _ _ _ _ _ _ _ hA hcub
  have h2 := genHasVal_mulGen hϖ D.toPre.P.L hL _ _ _ _ _ _ _ _ _ _ hB hC
  have := genHasVal_unique hϖ D.toPre.P.L hL _ _ _ _ _
    (genHasVal_corr hϖ D.toPre.P.L hL D.toPre.P.A.hom _ _ _ _ _ _ _ _
      (sumElim_sec hsA (fun _ => over_sec _ _)) (sumElim_sec hsB hsC) _ _
      (genHasVal_isGen D.toPre.P.L _ _ _ _ _ h2) (D.tau_bimult a a' b) h1) h2
  linarith

include hϖ in

theorem Q_neg (hQ : IsQ D.toPre ϖ Q) (χ : D.toPre.X) : Q (-χ) = Q χ := by
  have hL := D.toPre.P.isLB
  have hsym := genHasVal_pullGen_of (ϖ := ϖ) D.toPre.P.L _ _ D.toPre.sym D.toPre.sym_gen (D.toPre.c χ).left (D.toPre.xK χ)
    (ptK_eq D.toPre χ)
  have h1 := genHasVal_mulGen hϖ D.toPre.P.L hL _ _ _ _ _ _ _ _ _ _ (hQ (-χ)) hsym
  have := QVal_unique hϖ D
    (genHasVal_corr hϖ D.toPre.P.L hL D.toPre.P.A.hom _ _ _ _ _ _ _ _ (by secTac) (by secTac) _ _ (D.toPre.psi_gen χ) (D.psi_even χ) h1) (hQ χ)
  linarith

include hϖ in

theorem Q_zero (hQ : IsQ D.toPre ϖ Q) : Q 0 = 0 := by
  have h := bOf_add_left hϖ D hQ 0 0 0
  simp only [bOf, add_zero] at h
  linarith

theorem bOf_comm (χ χ' : D.toPre.X) : bOf D.toPre Q χ χ' = bOf D.toPre Q χ' χ := by
  unfold bOf
  rw [add_comm χ χ']
  ring

include hϖ in

theorem two_Q_eq (hQ : IsQ D.toPre ϖ Q) (χ : D.toPre.X) : 2 * Q χ = bOf D.toPre Q χ χ := by
  have h := bOf_add_left hϖ D hQ χ (-χ) χ
  have h0 := Q_zero hϖ D hQ
  have hn := Q_neg hϖ D hQ χ
  simp only [bOf, add_neg_cancel, zero_add, neg_add_cancel] at h
  simp only [bOf]
  linarith

include hϖ in

theorem Q_pos (hQ : IsQ D.toPre ϖ Q) {χ : D.toPre.X} (hχ : χ ≠ 0) : 1 ≤ Q χ := by
  have h := genHasVal_ge_of_in hϖ D.toPre.P.L D.toPre.P.isLB (D.toPre.c χ).left (D.toPre.xK χ) (ptK_eq D.toPre χ)
    (-1) (D.toPre.psi χ) 1 (fun j W hW hle h => by rw [pow_one]; exact D.psi_pos χ hχ j W hW hle h) (hQ χ)
  exact_mod_cast h

include hϖ in

def bHom (hQ : IsQ D.toPre ϖ Q) : D.toPre.X →+ D.toPre.X →+ ℤ :=
  AddMonoidHom.mk' (fun a => AddMonoidHom.mk' (fun b => bOf D.toPre Q a b) (fun b b' => by
      rw [bOf_comm D (Q := Q) a (b + b'), bOf_add_left hϖ D hQ, bOf_comm D (Q := Q) b a,
        bOf_comm D (Q := Q) b' a]))
    (fun a a' => by ext b; simp [bOf_add_left hϖ D hQ])

include hϖ in
lemma bHom_apply (hQ : IsQ D.toPre ϖ Q) (a b : D.toPre.X) : bHom hϖ D hQ a b = bOf D.toPre Q a b := rfl

include hϖ in

lemma gram_int_pos (hQ : IsQ D.toPre ϖ Q) {d : ℕ} (b : Module.Basis (Fin d) ℤ D.toPre.X) (m : Fin d → ℤ)
    (hm : m ≠ 0) : 0 < ∑ i, ∑ j, m i * bOf D.toPre Q (b i) (b j) * m j := by
  have hv : ∑ i, m i • b i ≠ 0 := by
    intro h0
    exact hm (funext fun i => Fintype.linearIndependent_iff.mp b.linearIndependent m h0 i)
  have lin : ∀ (a : D.toPre.X) (c : Fin d → ℤ),
      bOf D.toPre Q a (∑ i, c i • b i) = ∑ i, c i * bOf D.toPre Q a (b i) := by
    intro a c
    rw [← bHom_apply hϖ D hQ, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, bHom_apply hϖ D hQ]
    first
    | rfl
    | simp
    | exact zsmul_eq_mul _ _
  have hexp : bOf D.toPre Q (∑ i, m i • b i) (∑ i, m i • b i) =
      ∑ i, ∑ j, m i * bOf D.toPre Q (b i) (b j) * m j := by
    rw [lin]
    simp_rw [bOf_comm D (Q := Q) (∑ i, m i • b i), lin, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [bOf_comm D (Q := Q) (b j) (b i)]
    ring
  have h2 := two_Q_eq hϖ D hQ (∑ i, m i • b i)
  have h1 := Q_pos hϖ D hQ hv
  rw [← hexp]
  linarith

open Matrix in
include hϖ in

theorem gram_posDef (hQ : IsQ D.toPre ϖ Q) {d : ℕ} (b : Module.Basis (Fin d) ℤ D.toPre.X) :
    (Matrix.of fun i j => (bOf D.toPre Q (b i) (b j) : ℝ)).PosDef := by
  classical
  set G : Matrix (Fin d) (Fin d) ℝ := Matrix.of fun i j => (bOf D.toPre Q (b i) (b j) : ℝ) with hG
  set GQ : Matrix (Fin d) (Fin d) ℚ := Matrix.of fun i j => (bOf D.toPre Q (b i) (b j) : ℚ) with hGQ
  have hsymm : G.IsHermitian := by
    ext i j
    simp [G, Matrix.conjTranspose_apply, bOf_comm D (Q := Q) (b i) (b j)]

  have hratQ : ∀ x : Fin d → ℚ, x ≠ 0 → 0 < x ⬝ᵥ (GQ *ᵥ x) := by
    intro x hx
    obtain ⟨N, hN, hNx⟩ : ∃ N : ℕ, 0 < N ∧ ∀ i, ∃ z : ℤ, (N : ℚ) * x i = z := by
      refine ⟨∏ i, (x i).den, Finset.prod_pos fun i _ => (x i).den_pos, fun i => ?_⟩
      refine ⟨(x i).num * ∏ k ∈ Finset.univ.erase i, ((x k).den : ℤ), ?_⟩
      have h1 : ((∏ k, (x k).den : ℕ) : ℚ) = ((x i).den : ℚ) * ∏ k ∈ Finset.univ.erase i, ((x k).den : ℚ) := by
        push_cast; exact (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
      rw [h1]; push_cast; rw [← Rat.mul_den_eq_num (x i)]; ring
    choose m hm using hNx
    have hm0 : m ≠ 0 := by
      intro h0; apply hx; funext i
      have := hm i; rw [h0] at this; simp at this
      rcases this with h | h
      · exact absurd h (by exact_mod_cast hN.ne')
      · exact h
    have hpos := gram_int_pos hϖ D hQ b m hm0
    have hexp : ((N : ℚ) ^ 2) * (x ⬝ᵥ (GQ *ᵥ x)) = ((∑ i, ∑ j, m i * bOf D.toPre Q (b i) (b j) * m j : ℤ) : ℚ) := by
      simp only [dotProduct, Matrix.mulVec, GQ, Matrix.of_apply, Finset.mul_sum]
      push_cast
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      rw [← hm i, ← hm j]; ring
    have hN2 : (0 : ℚ) < (N : ℚ) ^ 2 := by positivity
    have : (0 : ℚ) < ((∑ i, ∑ j, m i * bOf D.toPre Q (b i) (b j) * m j : ℤ) : ℚ) := by exact_mod_cast hpos
    rw [← hexp] at this
    exact pos_of_mul_pos_right this hN2.le

  set f : (Fin d → ℝ) → ℝ := fun x => x ⬝ᵥ (G *ᵥ x) with hf
  have hcast : ∀ x : Fin d → ℚ, f (fun i => (x i : ℝ)) = ((x ⬝ᵥ (GQ *ᵥ x) : ℚ) : ℝ) := by
    intro x
    simp only [f, dotProduct, Matrix.mulVec, G, GQ, Matrix.of_apply]
    push_cast; rfl
  have hcont : Continuous f := by
    simp only [f, dotProduct, Matrix.mulVec]; fun_prop

  have hpsd : ∀ x, 0 ≤ f x := by
    have hdense : DenseRange (fun x : Fin d → ℚ => fun i => (x i : ℝ)) :=
      DenseRange.piMap (fun _ => Rat.denseRange_cast)
    intro x
    have hclosed : IsClosed {y | 0 ≤ f y} := isClosed_le continuous_const hcont
    have hsub : Set.range (fun x : Fin d → ℚ => fun i => (x i : ℝ)) ⊆ {y | 0 ≤ f y} := by
      rintro _ ⟨q, rfl⟩
      show 0 ≤ f _
      rw [hcast]
      by_cases hq : q = 0
      · subst hq; simp
      · exact_mod_cast (hratQ q hq).le
    exact (hclosed.closure_subset_iff.mpr hsub) (hdense x)

  have hdet : G.det ≠ 0 := by
    intro h0
    have hGmap : G = GQ.map (Rat.castHom ℝ) := by ext i j; simp [G, GQ]
    have hq0 : GQ.det = 0 := by
      have : ((GQ.det : ℚ) : ℝ) = 0 := by
        rw [← h0, hGmap]; exact RingHom.map_det (Rat.castHom ℝ) GQ
      exact_mod_cast this
    obtain ⟨v, hv, hGv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hq0
    have := hratQ v hv
    rw [hGv, dotProduct_zero] at this
    exact lt_irrefl _ this
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨hsymm, fun x hx => ?_⟩
  have hx' : star x = x := by ext i; simp
  rw [hx']
  rcases (hpsd x).lt_or_eq with h | h
  · exact h
  · exfalso

    have hGx : G *ᵥ x = 0 := by
      set y := G *ᵥ x
      have key : ∀ t : ℝ, 0 ≤ 2 * t * (y ⬝ᵥ y) + t ^ 2 * (y ⬝ᵥ (G *ᵥ y)) := by
        intro t
        have h1 := hpsd (x + t • y)
        have hsym' : ∀ u w : Fin d → ℝ, u ⬝ᵥ (G *ᵥ w) = w ⬝ᵥ (G *ᵥ u) := by
          intro u w
          rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
          have : Gᵀ = G := by ext i j; simp [G, bOf_comm D (Q := Q) (b i) (b j)]
          rw [this, dotProduct_comm]
        simp only [f, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct,
          dotProduct_smul, smul_dotProduct, smul_eq_mul] at h1
        have h' : x ⬝ᵥ (G *ᵥ x) = 0 := by simpa [f] using h.symm
        have e1 : x ⬝ᵥ (G *ᵥ y) = y ⬝ᵥ y := by rw [hsym' x y]
        have e2 : y ⬝ᵥ (G *ᵥ x) = y ⬝ᵥ y := rfl
        rw [h', e1, e2] at h1
        have : 2 * t * (y ⬝ᵥ y) + t ^ 2 * (y ⬝ᵥ (G *ᵥ y)) =
            0 + t * (y ⬝ᵥ y) + (t * (y ⬝ᵥ y) + t * (t * (y ⬝ᵥ (G *ᵥ y)))) := by ring
        linarith
      have hyy : y ⬝ᵥ y = 0 := by
        have c0 := hpsd y
        simp only [f] at c0
        set a := y ⬝ᵥ y
        set c := y ⬝ᵥ (G *ᵥ y)
        have k1 := key (-(a / (c + 1)))
        have hc1 : 0 < c + 1 := by linarith
        have ha : 0 ≤ a := by simp only [a, dotProduct, ← sq]; positivity
        by_contra hne
        have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm hne)
        have : 2 * (-(a / (c + 1))) * a + (-(a / (c + 1))) ^ 2 * c < 0 := by
          have hq : a / (c + 1) > 0 := div_pos ha' hc1
          have hq2 : (a / (c + 1)) * c ≤ a := by
            rw [div_mul_eq_mul_div, div_le_iff₀ hc1]; nlinarith
          nlinarith [hq2]
        linarith
      have := dotProduct_self_eq_zero.mp hyy
      exact this
    obtain ⟨v, hv, hv0⟩ : ∃ v, v ≠ 0 ∧ G *ᵥ v = 0 := ⟨x, hx, hGx⟩
    exact hdet (Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv, hv0⟩)

theorem exists_rosati_gen (hLaws : Laws) {O : Type} [Ring O] [StarRing O] [Module O D.toPre.X] (ιD : D.OAct O) (a : O) :
    ∃ u : LB.Gen (LB.LinComb D.toPre.P.L (rosatiφ D.toPre.P.A (ιD.onB.act a) (ιD.onB.act (star a))) rosatiε),
      u.IsGen ∧ LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ u (zero2 D.toPre.P.A))
        (LB.oneGen D.toPre.P.L) := by
  have := ιD.onB.hom a
  have := ιD.onB.hom (star a)
  exact ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_ros hLaws.globalFns D.toPre.P.isAb D.toPre.P.isLB _ _ (ιD.onB.rosati a)

include hϖ in

theorem bOf_balance (hLaws : Laws) {O : Type} [Ring O] [StarRing O] [Module O D.toPre.X] (ιD : D.OAct O)
    (hQ : IsQ D.toPre ϖ Q) (a : O) (χ χ' : D.toPre.X) :
    bOf D.toPre Q (a • χ) χ' = bOf D.toPre Q χ (star a • χ') := by
  have hL := D.toPre.P.isLB
  obtain ⟨u, hu, hnorm⟩ := exists_rosati_gen D hLaws ιD a
  have hc := ιD.tau_bal a u hu hnorm χ χ'
  obtain ⟨_, _, hsA, hA⟩ := tau_val hϖ D hQ (a • χ) χ'
  obtain ⟨_, _, hsB, hB⟩ := tau_val hϖ D hQ χ (star a • χ')
  have hu0 := genHasVal_pullGen_of (ϖ := ϖ) D.toPre.P.L _ _ u hu (lift (D.toPre.c χ) (D.toPre.c χ')).left
    (D.toPre.pt2 χ χ') (by simp [DegPre.pt2, ← CartesianMonoidalCategory.comp_lift])
  have h1 := genHasVal_mulGen hϖ D.toPre.P.L hL _ _ _ _ _ _ _ _ _ _ hA hu0
  have := genHasVal_unique hϖ D.toPre.P.L hL _ _ _ _ _
    (genHasVal_corr hϖ D.toPre.P.L hL D.toPre.P.A.hom _ _ _ _ _ _ _ _
      (sumElim_sec hsA (fun k => by
        obtain ⟨q, hq⟩ := rosatiφ_over D.toPre.P.A (ιD.onB.act a) (ιD.onB.act (star a)) k
        show (_ ≫ rosatiφ D.toPre.P.A (ιD.onB.act a) (ιD.onB.act (star a)) k) ≫ _ = _
        rw [hq]; exact over_sec _ _)) hsB _ _
      (genHasVal_isGen D.toPre.P.L _ _ _ _ _ hB) hc h1) hB
  linarith

end ReciprocityTheory.ChartRestriction.G.DVR.QForm
