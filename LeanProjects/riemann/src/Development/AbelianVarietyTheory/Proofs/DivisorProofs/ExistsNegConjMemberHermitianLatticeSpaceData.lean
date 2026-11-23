import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding
import Formalism.LocalToGlobal.Columns.BrpStarLatLattice

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.TripleSpace

theorem hasSig_neg_of_hasSignature {n p q : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : Formalism.UG.HasSignature M p q) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig (-M) q p := by
  obtain ⟨e, P, hP⟩ := h
  refine ⟨?_, ?_⟩
  · have := Fintype.card_congr e
    simp only [Fintype.card_fin, Fintype.card_sum] at this
    omega
  · let Q : Matrix (Fin n) (Fin q ⊕ Fin p) ℂ := (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).submatrix e Sum.swap
    refine ⟨Q.map star, ?_⟩
    have hQ : (Q.map star)ᵀ = Qᴴ := rfl
    have hQ2 : (Q.map star).map star = Q := by ext a b; simp
    rw [hQ, hQ2, Matrix.mul_neg, Matrix.neg_mul]
    have key : Qᴴ * M * Q = ((Formalism.UG.cT (starRingEnd ℂ) (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)) *
        Matrix.reindex e e M * (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)).submatrix Sum.swap Sum.swap := by
      have hc : Formalism.UG.cT (starRingEnd ℂ) (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) =
          (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)ᴴ := by ext a b; rfl
      have hM : M = (Matrix.reindex e e M).submatrix e e := by ext a b; simp
      have hQh : Qᴴ = (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)ᴴ.submatrix Sum.swap e := by
        simp only [Q, Matrix.conjTranspose_submatrix]
      rw [hc, hQh, hM, ← Matrix.submatrix_mul _ _ _ e _ e.bijective, Matrix.reindex_apply,
        Matrix.submatrix_submatrix]
      simp only [Q]
      rw [← Matrix.submatrix_mul _ _ _ e _ e.bijective]
      simp [Matrix.reindex_apply]
    rw [key, hP]
    ext a b
    rcases a with a | a <;> rcases b with b | b <;> simp [Formalism.UG.Jpq, Matrix.fromBlocks, Matrix.one_apply]

open Formalism.IndefR.Datum in

theorem isCartan_neg_conj {n : ℕ} {G s : Matrix (Fin n) (Fin n) ℂ} (h : IsCartanInv G s) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan (-(G.map star)) (-s) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hsG : sᴴ * G = G * s := by
    calc sᴴ * G = sᴴ * G * (s * s) := by rw [h1, Matrix.mul_one]
    _ = (sᴴ * G * s) * s := by simp only [Matrix.mul_assoc]
    _ = G * s := by rw [h2]
  have e2 : sᵀ * G.map star * s.map star = G.map star := by
    have := congrArg (fun X => X.map (starRingEnd ℂ)) h2
    simp only [Matrix.map_mul] at this
    have a1 : sᴴ.map (starRingEnd ℂ) = sᵀ := by ext a b; simp [Matrix.conjTranspose_apply]
    have a2 : ∀ M : Matrix (Fin n) (Fin n) ℂ, M.map (starRingEnd ℂ) = M.map star := fun M => rfl
    rw [a1, a2, a2] at this
    exact this
  refine ⟨by rw [neg_mul_neg, h1], ?_, ?_⟩
  · have e1 : (-s).map star = -(s.map star) := by ext a b; simp
    rw [e1, Matrix.transpose_neg]
    simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, e2]
  · intro x hx
    have hz := h3.dotProduct_mulVec_pos hx
    have hGs : (G.map star) *ᵥ star x = star (G *ᵥ x) := by
      ext i; simp [Matrix.mulVec, dotProduct, star_sum]
    have key : ((-s) *ᵥ x) ⬝ᵥ ((-(G.map star)) *ᵥ star x) = star (star x ⬝ᵥ (G * s) *ᵥ x) := by
      rw [Matrix.neg_mulVec, Matrix.neg_mulVec, neg_dotProduct, dotProduct_neg, neg_neg, hGs,
        ← star_star (s *ᵥ x), star_dotProduct_star]
      congr 1
      rw [star_mulVec, dotProduct_comm, ← dotProduct_mulVec, Matrix.mulVec_mulVec, hsG]
    rw [key, Complex.star_def, Complex.conj_re]
    exact (Complex.pos_iff.1 hz).1

theorem star_gram {D : D7} (V : HSp D) (a b : Fin V.rank) : star (V.gram a b) = V.gram b a :=
  V.herm.eq (V.frame a) (V.frame b)

theorem form_neg_eq {D : D7} (V : HSp D) (y x : Fin V.rank → D.host.E) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form D.sp.cm.sig ((-1 : D.host.E) • V.gram) y x =
      -star (∑ i, ∑ j, star ((star x) i) * V.gram i j * (star y) j) := by
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, dotProduct, Matrix.mulVec, Matrix.smul_apply, star_sum, Pi.star_apply,
    star_star, star_mul', star_gram, Finset.mul_sum, smul_eq_mul]
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  show y b * (-1 * V.gram b a * star (x a)) = -(star (x a) * V.gram b a * y b)
  ring

theorem mem_starLat_iff_form {D : D7} (V : HSp D) {Λ₀ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hsd : IsSelfDualC V Λ₀) (y : Fin V.rank → D.host.E) :
    y ∈ Formalism.L2.Col.starLat D.host.E Λ₀ ↔ ∀ x ∈ Formalism.L2.Col.starLat D.host.E Λ₀,
      IsIntegral ℤ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form D.sp.cm.sig ((-1 : D.host.E) • V.gram) y x) := by
  rw [Formalism.L2.Col.mem_starLat, hsd.2]
  constructor
  · intro H x hx
    obtain ⟨b, hb⟩ := H (star x) hx
    rw [form_neg_eq, ← hb]
    exact ((RingOfIntegers.isIntegral_coe b).map (starRingEnd D.host.E).toIntAlgHom).neg
  · intro H x hx
    have h := H (star x) (by rw [Formalism.L2.Col.mem_starLat, star_star]; exact hx)
    rw [form_neg_eq, star_star] at h
    have h2 := h.neg.map (starRingEnd D.host.E).toIntAlgHom
    rw [neg_neg] at h2
    exact ⟨⟨_, h2⟩, star_star (R := D.host.E) _⟩

theorem negConj_isHerm : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (W : G.Weil)
    (i j : Fin D.R.m) (B : Base D.host.F D.host.E) (τf : InfinitePlace D.host.F → D.what₂.Tau),
    (∀ w x, (B.emb w).1 x = conj (tauE D (τf w) x)) →
    ∃ (Λ : Submodule (𝓞 D.host.E) (Fin (spW₁ G i j).rank → D.host.E))
      (bas : ∀ v : HeightOneSpectrum (𝓞 D.host.F), GL (Fin (spW₁ G i j).rank) (Fv D.host.F v)),
      Spc.IsHerm D.sp.cm.sig B
        (Spc.mk ((-1 : D.host.E) • (spW₁ G i j).gram) Λ (fun w => -W.cart (.grid (i : ℕ) (j : ℕ)) (τf w)) bas)
        ((D.R.m - j) / 2) ((spW₁ G i j).rank - (D.R.m - j) / 2) := by
  intro D T L sc G μ₀ hL W i j B τf hB
  have hR : Node.InRange D.R.m (.grid (i : ℕ) (j : ℕ)) := ⟨i.2.le, j.2.le⟩
  have hV := node_isV G hL hR
  have hsd : IsSelfDualC (spW₁ G i j) (G.Λ (.grid (i : ℕ) (j : ℕ))) := hV.sd
  have hlat : Submodule.IsLattice D.host.E (Formalism.L2.Col.starLat D.host.E (G.Λ (.grid (i : ℕ) (j : ℕ)))) :=
    Formalism.L2.Col.brp_starLat_lattice _ _ hsd.1
  have hb : ∀ v : B.P, ∃ β, GlobalTheory.AdelicU.IsSplitBasis (B.τ v) (Formalism.L2.Col.starLat D.host.E (G.Λ (.grid (i : ℕ) (j : ℕ)))) β :=
    fun v => GlobalTheory.AdelicU.exists_isSplitBasis (B.τ v) _ (GlobalTheory.AdelicU.isCMExt_host D)
  refine ⟨Formalism.L2.Col.starLat D.host.E (G.Λ (.grid (i : ℕ) (j : ℕ))),
    fun v => if h : v ∈ B.P then (hb ⟨v, h⟩).choose else 1, ⟨?_, ?_, hlat, ?_, ?_, ?_⟩⟩
  · intro a b
    show star (((-1 : D.host.E) • (spW₁ G i j).gram) b a) = ((-1 : D.host.E) • (spW₁ G i j).gram) a b
    simp only [Matrix.smul_apply, smul_eq_mul, star_mul', star_neg, star_one, star_gram]
  · intro w
    have hs := hV.sigOK (B.emb w).1
    rw [hV.sig, ← hV.rank] at hs
    have eJ : ((-1 : D.host.E) • (spW₁ G i j).gram).map (B.emb w).1 = -((spW₁ G i j).gram.map (B.emb w).1) := by
      ext a b; simp
    show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig (((-1 : D.host.E) • (spW₁ G i j).gram).map (B.emb w).1) _ _
    rw [eJ]
    exact hasSig_neg_of_hasSignature hs
  · intro y
    exact mem_starLat_iff_form (spW₁ G i j) hsd y
  · intro w
    have eJ : ((-1 : D.host.E) • (spW₁ G i j).gram).map (B.emb w).1 =
        -((gramAt D (spW₁ G i j) (τf w)).map star) := by
      ext a b; simp [gramAt, hB]
    show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan (((-1 : D.host.E) • (spW₁ G i j).gram).map (B.emb w).1) _
    rw [eJ]
    exact isCartan_neg_conj (W.cart_is _ hR (τf w))
  · intro v
    show GlobalTheory.AdelicU.IsSplitBasis _ _ (if h : v.1 ∈ B.P then (hb ⟨v.1, h⟩).choose else 1)
    rw [dif_pos v.2]
    exact (hb v).choose_spec

end GlobalTheory.TripleSpace
