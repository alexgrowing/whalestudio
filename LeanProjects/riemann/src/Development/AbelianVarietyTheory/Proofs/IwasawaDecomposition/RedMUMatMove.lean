import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinCongMemLevEnv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsSpanOfOnto
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetReducedBlockEqResidueDet
import Development.AbelianVarietyTheory.Proofs.HeightProofs.DetSubMemOfConj
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FinitePartPreservesFormDetNormOneStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.Datum
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdjMove

section Ring

variable {A R k : Type} [CommRing A] [CommRing R] [CommRing k] {m n : ℕ}

def adj (φ : A →+* R) (C : Matrix (Fin m) (Fin m) R) (B : Matrix (Fin n) (Fin n) R) (Z : Fin m → Fin n → A) :
    Matrix (Fin m) (Fin n) R := C * (Matrix.of Z).map φ * B

theorem adj_move (φ : A →+* R) (C : Matrix (Fin m) (Fin m) R) (B Y : Matrix (Fin n) (Fin n) R)
    (u : Matrix (Fin n) (Fin n) A) (h : (u.map φ)ᵀ * B * Y = B) (M : ℕ) (Z Z' w : Fin m → Fin n → A)
    (hZ : ∀ b, u *ᵥ Z' b = Z b + M • w b) : adj φ C B Z' = (adj φ C B Z + M • adj φ C B w) * Y := by
  have e : (Matrix.of Z).map φ + M • (Matrix.of w).map φ = (Matrix.of Z').map φ * (u.map φ)ᵀ := by
    ext b a
    have := congrArg φ (congrFun (hZ b) a)
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Pi.add_apply, Pi.smul_apply, map_add, map_nsmul] at this
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.of_apply, Matrix.mul_apply,
      Matrix.transpose_apply, ← this, mul_comm]
  unfold adj
  rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← Matrix.add_mul, ← Matrix.mul_add, e]
  conv_lhs => rw [← h]
  simp only [Matrix.mul_assoc]

theorem adj_apply (φ : A →+* R) (C : Matrix (Fin m) (Fin m) R) (B : Matrix (Fin n) (Fin n) R) (Z : Fin m → Fin n → A)
    (b' : Fin m) (a : Fin n) : adj φ C B Z b' a = ∑ b, C b' b * ∑ j, φ (Z b j) * B j a := by
  unfold adj
  rw [Matrix.mul_assoc]
  simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply]

theorem red_eq (S : Subring R) (ρ : S →+* k) (M : ℕ) (hM : (M : k) = 0) (X X' W : Matrix (Fin m) (Fin n) R)
    (y : Matrix (Fin n) (Fin n) S) (hX : ∀ i j, X i j ∈ S) (hX' : ∀ i j, X' i j ∈ S) (hW : ∀ i j, W i j ∈ S)
    (h : X' = (X + M • W) * y.map S.subtype) (i : Fin m) (j : Fin n) :
    ρ ⟨X' i j, hX' i j⟩ = ∑ a, ρ ⟨X i a, hX i a⟩ * ρ (y a j) := by
  have e : (⟨X' i j, hX' i j⟩ : S) = ∑ a, (⟨X i a, hX i a⟩ + M • ⟨W i a, hW i a⟩) * y a j := by
    apply Subtype.ext
    simp [h, Matrix.mul_apply]
  rw [e, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul, map_add, map_nsmul, nsmul_eq_mul, hM, zero_mul, add_zero]

def lft (c : R) (P Q : Matrix (Fin m) (Fin m) R) : Matrix (Fin m) (Fin m) R := c • (P * Q)

theorem entry_eq {E : Type} [CommRing E] (f : E →+* R) (φ : A →+* R) (c : R) (P : Matrix (Fin m) (Fin m) R)
    (Q : Matrix (Fin m) (Fin m) E) (X : Matrix (Fin m) (Fin n) E) (G : Matrix (Fin n) (Fin n) E)
    (β : Matrix (Fin n) (Fin n) R) (Z : Fin m → Fin n → A) (h : ∀ b a, f (X b a) = φ (Z b a)) :
    (fun b a => c * (P * (Q * X * G).map f * β) b a) = adj φ (lft c P (Q.map f)) (G.map f * β) Z := by
  have e1 : X.map f = (Matrix.of Z).map φ := Matrix.ext h
  unfold adj lft
  rw [Matrix.smul_mul, Matrix.smul_mul, ← e1, Matrix.map_mul, Matrix.map_mul]
  ext b a
  simp only [Matrix.mul_assoc, Matrix.smul_apply, smul_eq_mul]

theorem unit_rel_ring (S : Subring R) (σ : A →+* A) (s : A →+* R) (J : Matrix (Fin n) (Fin n) A) (u : GL (Fin n) A)
    (β : GL (Fin n) R) (y : GL (Fin n) S) (hu : u ∈ Formalism.UG.UJ σ J)
    (hy : β * Formalism.UG.bc S.subtype y * β⁻¹ = Formalism.UG.bc s u) :
    (u.1.map (s.comp σ))ᵀ * (J.map s * β.1) * y.1.map S.subtype = J.map s * β.1 := by
  have h1 : β * Formalism.UG.bc S.subtype y = Formalism.UG.bc s u * β := by rw [← hy, inv_mul_cancel_right]
  have h2 : β.1 * y.1.map S.subtype = u.1.map s * β.1 := congrArg Units.val h1
  have h4 : (u.1.map σ)ᵀ * J * u.1 = J := hu
  have h5 := congrArg (fun N => Matrix.map N s) h4
  simp only [Matrix.map_mul] at h5
  have h6 : (u.1.map (s.comp σ))ᵀ * J.map s * u.1.map s = J.map s := h5
  rw [Matrix.mul_assoc, Matrix.mul_assoc, h2, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h6]

theorem adj_int_ring (S : Subring R) (φ : A →+* R) (C : Matrix (Fin m) (Fin m) R) (B : Matrix (Fin n) (Fin n) R)
    (s : Set (Fin n → A)) (La : Type) [Zero La] (v : La → Fin n → A) (v0 : ∀ j, v 0 j = 0)
    (h : ∀ x : Fin m → La, ∀ i j, adj φ C B (fun b => v (x b)) i j ∈ S)
    (hs : ∀ z ∈ s, ∃ t ∈ S, ∃ l, ∀ j, φ (z j) = t * φ (v l j))
    (w : Fin m → Fin n → A) (hw : ∀ b, w b ∈ AddSubgroup.closure s) (b' : Fin m) (a : Fin n) : adj φ C B w b' a ∈ S := by
  rw [adj_apply]
  refine sum_mem fun b _ => ?_
  have key : ∀ z ∈ AddSubgroup.closure s, C b' b * ∑ j, φ (z j) * B j a ∈ S := by
    intro z hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨t, ht, l, hl⟩ := hs z hz
      have h1 := h (Pi.single b l) b' a
      rw [adj_apply, Finset.sum_eq_single b] at h1
      · have h2 := mul_mem ht h1
        rw [Pi.single_eq_same, mul_left_comm, Finset.mul_sum] at h2
        simpa only [hl, mul_assoc] using h2
      · intro c _ hc
        rw [Pi.single_eq_of_ne hc]
        simp [v0]
      · simp
    | zero => simp
    | add x y _ _ hx hy =>
      simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib, mul_add]
      exact add_mem hx hy
    | neg x _ hx =>
      simp only [Pi.neg_apply, map_neg, neg_mul, Finset.sum_neg_distrib, mul_neg]
      exact neg_mem hx
  exact key _ (hw b)

end Ring

variable {D : D7}

noncomputable def barSwap (D : D7) : Af D.host.F ⊗[D.host.F] D.host.E →+* EAf D :=
  (Lev.swapAE D).comp (sigR (Af D.host.F) D.sp.cm.sig)

theorem barSwap_tmul (a : Af D.host.F) (x : D.host.E) :
    barSwap D (a ⊗ₜ[D.host.F] x) = ((1 : D.host.E) ⊗ₜ[D.host.F] a) * barSwap D ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) := by
  change D.sp.cm.sig x ⊗ₜ[D.host.F] a = ((1 : D.host.E) ⊗ₜ[D.host.F] a) * (D.sp.cm.sig x ⊗ₜ[D.host.F] 1)
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

theorem uMat_eq (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (e : AE D)
    (X : Fin S.rank → Fin T.rank → D.host.E) :
    uMat S T βS βT e X = adj (barSwap D) (lft (toEAf D e) (βS⁻¹).1 (S.gram⁻¹.map (eToEAf D)))
      (T.gram.map (eToEAf D) * βT.1) fun b => finVec T (X b) :=
  entry_eq (eToEAf D) (barSwap D) _ _ _ _ _ _ _ fun _ _ => rfl

theorem unit_rel (T : HSp D) (βT : GL (Fin T.rank) (EAf D)) (u : GA D T)
    (y : GL (Fin T.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)) (hy : frGL βT y = Lev.finE T u) :
    ((finHom T u).1.map (barSwap D))ᵀ * (T.gram.map (eToEAf D) * βT.1) * y.1.map (Subring.subtype _) =
      T.gram.map (eToEAf D) * βT.1 :=
  unit_rel_ring _ (sigR (Af D.host.F) D.sp.cm.sig) (Lev.swapAE D) (JR (Af D.host.F) T.gram) (finHom T u) βT y
    (GlobalTheory.UnitarySplit.finHom_mem T u) hy

theorem adj_int {m : ℕ} (T : HSp D) (C : Matrix (Fin m) (Fin m) (EAf D)) (B : Matrix (Fin T.rank) (Fin T.rank) (EAf D))
    (La : Type) [AddCommGroup La] [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin T.rank → D.host.E))
    (h : ∀ x : Fin m → La, IsIntM (adj (barSwap D) C B fun b => finVec T (ι (x b))))
    (w : Fin m → Fin T.rank → Af D.host.F ⊗[D.host.F] D.host.E)
    (hw : ∀ b, w b ∈ GlobalTheory.AdLat.hat D.host.F (Set.range ι)) : IsIntM (adj (barSwap D) C B w) := by
  refine adj_int_ring _ (barSwap D) C B _ La (fun l => finVec T (ι l)) (fun j => ?_) h ?_ w hw
  · show (1 : Af D.host.F) ⊗ₜ[D.host.F] (ι 0 j) = 0
    rw [LinearMap.map_zero]
    exact TensorProduct.tmul_zero _ _
  · rintro z ⟨α, hα, _, ⟨l, rfl⟩, rfl⟩
    exact ⟨(1 : D.host.E) ⊗ₜ[D.host.F] α, Subring.subset_closure (Or.inr ⟨⟨α, hα⟩, rfl⟩), l,
      fun j => barSwap_tmul α (ι l j)⟩

set_option maxHeartbeats 800000 in

theorem redM_uMat_move : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (e : AE D) (La : Type) [AddCommGroup La] [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin T.rank → D.host.E)), (∀ x : Fin S.rank → La, IsIntM (uMat S T βS βT e fun b => ι (x b))) → ∀ (u : GA D T) (y : GL (Fin T.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)), frGL βT y = Lev.finE T u → ∀ (M : ℕ) (PP : Pl D.host.E), (M : 𝓞 D.host.E) ∈ PP.asIdeal → ∀ x x' : Fin S.rank → La, (∀ b, ∃ w ∈ GlobalTheory.AdLat.hat D.host.F (Set.range ι), (finHom T u).1.mulVec (finVec T (ι (x' b))) = finVec T (ι (x b)) + M • w) → redM PP (uMat S T βS βT e fun b => ι (x' b)) = redM PP (uMat S T βS βT e fun b => ι (x b)) * y.1.map (resS D.host.F PP) := by
  intro D S T βS βT e La _ _ ι hint u y hy M PP hM x x' hx
  choose w hw hx using hx
  have hW := adj_int T _ _ La ι (fun x => by rw [← uMat_eq S T βS βT e]; exact hint x) w hw
  have hmv := adj_move (barSwap D) (lft (toEAf D e) (βS⁻¹).1 (S.gram⁻¹.map (eToEAf D))) _ _ _ (unit_rel T βT u y hy) M
    (fun b => finVec T (ι (x b))) (fun b => finVec T (ι (x' b))) w hx
  rw [← uMat_eq S T βS βT e, ← uMat_eq S T βS βT e] at hmv
  have hM' : (M : kP PP) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk PP.asIdeal)]
    exact Ideal.Quotient.eq_zero_iff_mem.2 hM
  ext i j
  have := red_eq _ (resS D.host.F PP) M hM' _ _ _ y.1 (hint x) (hint x') hW hmv i j
  rw [Matrix.mul_apply]
  unfold redM
  rw [dif_pos (hint x' i j), this]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [dif_pos (hint x i a)]
  rfl

end GlobalTheory.AdjMove
