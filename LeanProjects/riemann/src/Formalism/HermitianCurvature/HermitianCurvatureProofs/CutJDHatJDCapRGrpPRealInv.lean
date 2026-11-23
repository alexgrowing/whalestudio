import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpP
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatQMinOp
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

def JDRInvFn : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (Y : ℂ) (p : B.SS k r), D.inSS p →
    ∀ F : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ((r + k : ℕ) : ℕ∞) (B.GV k r) F →
      ∀ g ∈ B.GPos D, rhatOp k r D.z D.z' Y (B.rho D p F) g = B.rho D p (rhatOp k r D.z D.z' Y F) g

section poly

open Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra

variable {k r : ℕ}

theorem ri_mul_left {a : ℕ} {P : Q.Mx k r → ℂ} (c : ℂ) (h : U.IsPolyDeg a P) :
    U.IsPolyDeg a (fun g => c * P g) := by
  obtain ⟨q, hq, hP⟩ := h
  refine ⟨MvPolynomial.C c * q, ?_, fun g => by simp [hP g]⟩
  calc (MvPolynomial.C c * q).totalDegree ≤ (MvPolynomial.C c).totalDegree + q.totalDegree :=
        MvPolynomial.totalDegree_mul _ _
    _ ≤ a := by simp [hq]

theorem ri_mul_right {a : ℕ} {P : Q.Mx k r → ℂ} (h : U.IsPolyDeg a P) (c : ℂ) :
    U.IsPolyDeg a (fun g => P g * c) := by
  obtain ⟨q, hq, hP⟩ := h
  refine ⟨q * MvPolynomial.C c, ?_, fun g => by simp [hP g]⟩
  calc (q * MvPolynomial.C c).totalDegree ≤ q.totalDegree + (MvPolynomial.C c).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
    _ ≤ a := by simp [hq]

theorem ri_ginv (v : Fin (2 * r + k + 1) → ℂ) (p : Fin (2 * r + k + 1)) :
    U.IsPolyDeg 1 (fun g => (ginvH k r g *ᵥ v) p) := by
  have hdeg : ∀ (a : ℂ) (i : (Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) ⊕ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1))),
      (MvPolynomial.C a * MvPolynomial.X i : MvPolynomial _ ℂ).totalDegree ≤ 1 := fun a i =>
    (MvPolynomial.totalDegree_mul _ _).trans (by simp)
  refine ⟨∑ c, ∑ b, ∑ a, MvPolynomial.C (Hpk k r p a * Hpk k r b c * v c) * MvPolynomial.X (Sum.inr (b, a)),
    ?_, fun g => ?_⟩
  · exact (MvPolynomial.totalDegree_finset_sum _ _).trans (Finset.sup_le fun c _ =>
      (MvPolynomial.totalDegree_finset_sum _ _).trans (Finset.sup_le fun b _ =>
        (MvPolynomial.totalDegree_finset_sum _ _).trans (Finset.sup_le fun a _ => hdeg _ _)))
  · simp only [ginvH, Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.conjTranspose_apply, map_sum,
      MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, Sum.elim_inr, Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
    ring

theorem ri_colR (z : Fin (2 * r + k + 1) → ℂ) (J : Fin (r + k) → Fin (2 * r + k + 1)) (q p : Fin (2 * r + k + 1)) :
    U.IsPolyDeg 1 (fun g => colR k r z g J q p) := by
  by_cases h1 : (q : ℕ) < r
  · simp only [colR, dif_pos h1]
    exact ri_ginv _ p
  · by_cases h2 : (q : ℕ) = r
    · simp only [colR, dif_neg h1, dif_pos h2]
      exact ri_ginv z p
    · refine ⟨MvPolynomial.C (colR k r z 0 J q p), by simp, fun g => ?_⟩
      simp [colR, h1, h2]

theorem ri_beJ (z : Fin (2 * r + k + 1) → ℂ) (J : Fin (r + k) → Fin (2 * r + k + 1)) :
    U.IsPolyDeg (2 * r + k + 1) (fun g => beJ k r z g J) := by
  choose Pq hPdeg hPev using fun q p => ri_colR (k := k) (r := r) z J q p
  refine ⟨(Matrix.of fun p q => Pq q p).det, ?_, fun g => ?_⟩
  · rw [Matrix.det_apply']
    refine (MvPolynomial.totalDegree_finset_sum _ _).trans (Finset.sup_le fun σ _ => ?_)
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    have h0 : (((Equiv.Perm.sign σ : ℤ) : MvPolynomial
        ((Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) ⊕ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) ℂ)).totalDegree = 0 := by
      have hc : ((Equiv.Perm.sign σ : ℤ) : MvPolynomial
          ((Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) ⊕ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) ℂ) =
          MvPolynomial.C ((Equiv.Perm.sign σ : ℤ) : ℂ) := by simp
      rw [hc]
      exact MvPolynomial.totalDegree_C _
    rw [h0, zero_add]
    refine (MvPolynomial.totalDegree_finset_prod _ _).trans ?_
    calc ∑ i, (Matrix.of (fun p q => Pq q p) (σ i) i).totalDegree ≤ ∑ _i : Fin (2 * r + k + 1), 1 :=
          Finset.sum_le_sum fun i _ => hPdeg _ _
      _ = 2 * r + k + 1 := by simp
  · show (Matrix.of fun p q => colR k r z g J q p).det = _
    rw [RingHom.map_det]
    congr 1
    ext p q
    simp [RingHom.mapMatrix_apply, hPev]

end poly

section ops

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem ri_order_le {t κ : ℕ} : ∀ Θ : B.DiffOp k r Wp Wq, PolyOp t κ Θ → B.opOrder Θ ≤ t
  | [], _ => by simp [B.opOrder]
  | Tm :: Θ, h => by
    have h1 := (h Tm (List.mem_cons_self ..)).1
    have h2 := ri_order_le Θ fun T' hT' => h T' (List.mem_cons_of_mem _ hT')
    unfold B.opOrder at h2 ⊢
    simp only [List.map_cons, List.foldr_cons]
    exact max_le h1 h2

def riCat (Θs : Fin (k + 1) → B.DiffOp k r Wp Wq) : List (Fin (k + 1)) → B.DiffOp k r Wp Wq
  | [] => []
  | i :: l => Θs i ++ riCat Θs l

theorem riCat_poly {Θs : Fin (k + 1) → B.DiffOp k r Wp Wq} {t κ : ℕ} (h : ∀ i, PolyOp t κ (Θs i)) :
    ∀ l, PolyOp t κ (riCat Θs l)
  | [] => fun T hT => absurd hT List.not_mem_nil
  | i :: l => QMinOp.polyOp_append (h i) (riCat_poly h l)

theorem riCat_apply (Θs : Fin (k + 1) → B.DiffOp k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r) :
    ∀ l, B.opApply (riCat Θs l) F g = (l.map fun i => B.opApply (Θs i) F g).sum
  | [] => by simp [riCat, B.opApply]
  | i :: l => by rw [riCat, QMinOp.opApply_append, riCat_apply Θs F g l, List.map_cons, List.sum_cons]

private theorem foldr_max_eq_max_foldr_max_zero : ∀ (L : List ℕ) (x : ℕ), L.foldr max x = max (L.foldr max 0) x := by
  intro L
  induction L with
  | nil => intro x; simp
  | cons y L ih => intro x; simp only [List.foldr_cons]; rw [ih x, max_assoc]

theorem riCat_order {Θs : Fin (k + 1) → B.DiffOp k r Wp Wq} {t κ : ℕ} (h : ∀ i, PolyOp t κ (Θs i))
    (ho : ∀ i, B.opOrder (Θs i) = t) (i : Fin (k + 1)) (l : List (Fin (k + 1))) :
    B.opOrder (riCat Θs (i :: l)) = t := by
  have hle : B.opOrder (riCat Θs l) ≤ t := ri_order_le _ (riCat_poly h l)
  have h1 := ho i
  simp only [B.opOrder] at h1 hle
  simp only [riCat, B.opOrder, List.map_append, List.foldr_append]
  rw [foldr_max_eq_max_foldr_max_zero, h1]
  exact max_eq_left hle

theorem ri_real (z z' : Fin (2 * r + k + 1) → ℂ) (Y ε : ℂ) :
    ∃ Θ : B.DiffOp k r Wp Wq, PolyOp (r + k) (2 * r + k + 1) Θ ∧ B.opOrder Θ = r + k ∧
      ∀ (UU : Set (B.Mat k r)) (F : B.Mat k r → (Wq →L[ℂ] Wp)), B.CkOn ((r + k : ℕ) : ℕ∞) UU F →
        ∀ g ∈ UU, g ∈ B.GV k r → B.opApply Θ F g = ε • rhatOp k r z z' Y F g := by
  have h : ∀ i : Fin (k + 1), ∃ Θ : B.DiffOp k r Wp Wq, PolyOp (r + k) (2 * r + k + 1) Θ ∧ B.opOrder Θ = r + k ∧
      ∀ (UU : Set (B.Mat k r)) (F : B.Mat k r → (Wq →L[ℂ] Wp)), B.CkOn ((r + k : ℕ) : ℕ∞) UU F →
        ∀ g ∈ UU, g ∈ B.GV k r → B.opApply Θ F g = ∑ J ∈ jSetR k r,
          (fun (J : Fin (r + k) → Fin (2 * r + k + 1)) (g : B.Mat k r) =>
            ε * (((-1 : ℂ) ^ (i : ℕ)) * herm (Hpk k r) (bvec (wI k r i)) z' * beJ k r z g J)) J g •
            qminorOp (Q.EH k r) (rowsR k r i) J (Q.uC k r 0 Y) F g := fun i =>
    QMinOp.qminOpRep (jSetR k r) (rowsR k r i) (fun J => J) _
      (fun J _ => ri_mul_left _ (ri_mul_left _ (ri_beJ z J))) _
  choose Θs hP hO hR using h
  refine ⟨riCat Θs (List.finRange (k + 1)), riCat_poly hP _, ?_, ?_⟩
  · have e : List.finRange (k + 1) = (0 : Fin (k + 1)) :: (List.finRange k).map Fin.succ := List.finRange_succ
    rw [e]
    exact riCat_order hP hO _ _
  · intro UU F hF g hgU hg
    rw [riCat_apply, ← Fin.sum_univ_def]
    simp only [rhatOp, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hR i UU F hF g hgU hg]
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [smul_smul]

end ops

theorem jDRRealInvP_of_inv (hI : JDRInvFn) : JDRRealInvP := by
  intro ε Cc E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v y
  obtain ⟨Θ, hP, hO, hR⟩ := ri_real (Wp := Wp (S.pl v)) (Wq := Wq (S.pl v)) (T v).base.z (T v).base.z' (y : ℂ) ε
  have hn : 0 < 2 * S.G.r + S.G.k + 1 := by omega
  refine ⟨Θ, QMinOp.polyOp_mono hP (by omega) (Nat.le_mul_of_pos_left _ (by omega)), ?_, ?_⟩
  · intro p hp F hF g hg
    rw [hO] at hF
    have hgG : g ∈ B.GV S.G.k S.G.r := hg.1
    have hsg : B.sgs p g ∈ B.GV S.G.k S.G.r := Formalism.FourierDecayAlt.P.B6.conj_product_mem_unitary_group (T v).base hp hgG
    rw [hR _ _ (Formalism.FourierDecayAlt.P.B5.ckOn_rho (T v).base hp hF) g hgG hgG]
    have e2 : B.rho (T v).base p (B.opApply Θ F) g =
        B.rho (T v).base p (fun x => ε • rhatOp S.G.k S.G.r (T v).base.z (T v).base.z' (y : ℂ) F x) g := by
      simp only [B.rho]
      rw [hR _ _ hF _ hsg hsg]
    rw [e2, hI S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) (T v).base (y : ℂ) p hp F hF g hg]
    simp only [B.rho, ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp]
  · intro U F hU hF g hg
    have hgG : g ∈ B.GV S.G.k S.G.r := by simpa [Q.Glev] using hg.1
    refine hR (Q.Glev S.G.k S.G.r 0 ∩ U) F ?_ g hg hgG
    intro g₀ hg₀
    obtain ⟨U', F', hU', hg₀U, hc, he⟩ := hF g₀ hg₀
    refine ⟨U', F', hU', hg₀U, hc.of_le (by exact_mod_cast le_top), fun x hx hxG => he x hx ?_⟩
    simpa [Q.Glev] using hxG

end

end Formalism.FourierDecayAlt.P.CutMP
