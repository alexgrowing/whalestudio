import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Statements.GeometryStatements.NineGeoU
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentDataHodgeThirdStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentDataHodgeFourthStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BlockMatrixGramNormalStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GramMatrixTwoFramesStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GramMatrixChangeFrameStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.InteriorPointPolarisedStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SmallGram

def blockEquiv {j N : ℕ} (hj : j ≤ N) : Fin j ⊕ Fin (N - j) ≃ Fin N :=
  finSumFinEquiv.trans (finCongr (by omega))

theorem blockEquiv_inl {j N : ℕ} (hj : j ≤ N) (a : Fin j) : blockEquiv hj (Sum.inl a) = headIdx hj a := by
  ext; simp [blockEquiv, headIdx]

theorem blockEquiv_inr {j N : ℕ} (hj : j ≤ N) (k : Fin (N - j)) : blockEquiv hj (Sum.inr k) = tailIdx hj k := by
  ext; simp [blockEquiv, tailIdx]

theorem sum_blocks {M : Type} [AddCommMonoid M] {j N : ℕ} (hj : j ≤ N) (f : Fin N → M) :
    ∑ p, f p = ∑ a, f (headIdx hj a) + ∑ k, f (tailIdx hj k) := by
  rw [← (blockEquiv hj).sum_comp, Fintype.sum_sum_type]
  simp only [blockEquiv_inl, blockEquiv_inr]

theorem headIdx_injective {j N : ℕ} (hj : j ≤ N) : Function.Injective (headIdx hj) := by
  intro a a' h
  rw [← blockEquiv_inl, ← blockEquiv_inl] at h
  simpa using (blockEquiv hj).injective h

theorem tailIdx_injective {j N : ℕ} (hj : j ≤ N) : Function.Injective (tailIdx hj) := by
  intro a a' h
  rw [← blockEquiv_inr, ← blockEquiv_inr] at h
  simpa using (blockEquiv hj).injective h

def blk {R : Type} [CommRing R] {j N : ℕ} (hj : j ≤ N) (C : Matrix (Fin j) (Fin (N - j)) R) :
    Matrix (Fin N) (Fin N) R :=
  Matrix.reindex (blockEquiv hj) (blockEquiv hj) (Matrix.fromBlocks 1 C 0 1)

section GlobalTheory

variable {R : Type} [CommRing R] {j N : ℕ} (hj : j ≤ N) (C : Matrix (Fin j) (Fin (N - j)) R)

theorem blk_hh (a a' : Fin j) : blk hj C (headIdx hj a) (headIdx hj a') = if a = a' then 1 else 0 := by
  simp [blk, ← blockEquiv_inl, Matrix.one_apply]

theorem blk_ht (a : Fin j) (k : Fin (N - j)) : blk hj C (headIdx hj a) (tailIdx hj k) = C a k := by
  simp [blk, ← blockEquiv_inl, ← blockEquiv_inr]

theorem blk_th (a : Fin j) (k : Fin (N - j)) : blk hj C (tailIdx hj k) (headIdx hj a) = 0 := by
  simp [blk, ← blockEquiv_inl, ← blockEquiv_inr]

theorem blk_tt (k k' : Fin (N - j)) : blk hj C (tailIdx hj k) (tailIdx hj k') = if k = k' then 1 else 0 := by
  simp [blk, ← blockEquiv_inr, Matrix.one_apply]

theorem det_blk : (blk hj C).det = 1 := by
  simp [blk, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]

end GlobalTheory

section Frame

variable {Ω : Type} [Field Ω] {V : Type} [AddCommGroup V] [Module Ω V] {j N : ℕ} (hj : j ≤ N)

def replaceTail (b : Fin N → V) (x : Fin (N - j) → V) : Fin N → V :=
  fun p => Sum.elim (b ∘ headIdx hj) x ((blockEquiv hj).symm p)

theorem replaceTail_head (b : Fin N → V) (x : Fin (N - j) → V) (a : Fin j) :
    replaceTail hj b x (headIdx hj a) = b (headIdx hj a) := by
  simp [replaceTail, ← blockEquiv_inl]

theorem replaceTail_tail (b : Fin N → V) (x : Fin (N - j) → V) (k : Fin (N - j)) :
    replaceTail hj b x (tailIdx hj k) = x k := by
  simp [replaceTail, ← blockEquiv_inr]

theorem exists_coeff (A : Subring Ω) {b : Fin N → V} (hb : LinearIndependent Ω b) {x : Fin (N - j) → V}
    (h1 : ∀ k, b (tailIdx hj k) - x k ∈ Submodule.span A (Set.range b))
    (h2 : ∀ k, b (tailIdx hj k) - x k ∈ Submodule.span Ω (Set.range (b ∘ headIdx hj))) :
    ∃ C : Matrix (Fin j) (Fin (N - j)) Ω, (∀ a k, C a k ∈ A) ∧
      ∀ k, x k = b (tailIdx hj k) + ∑ a, C a k • b (headIdx hj a) := by
  have key : ∀ k, ∃ c : Fin j → Ω, (∀ a, c a ∈ A) ∧ x k = b (tailIdx hj k) + ∑ a, c a • b (headIdx hj a) := by
    intro k
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun A).1 (h1 k)
    obtain ⟨c', hc'⟩ := (Submodule.mem_span_range_iff_exists_fun Ω).1 (h2 k)
    have hz : ∑ p, (((c p : A) : Ω) - Sum.elim c' (fun _ => 0) ((blockEquiv hj).symm p)) • b p = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [sum_blocks hj (fun p => Sum.elim c' (fun _ => (0 : Ω)) ((blockEquiv hj).symm p) • b p)]
      have e1 : ∑ p, ((c p : A) : Ω) • b p = b (tailIdx hj k) - x k := hc
      simp only [← blockEquiv_inl, ← blockEquiv_inr, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr, zero_smul,
        Finset.sum_const_zero, add_zero]
      simp only [blockEquiv_inl]
      rw [e1, sub_eq_zero]
      exact hc'.symm
    have h0 := Fintype.linearIndependent_iff.1 hb _ hz
    have hca : ∀ a, c' a = ((c (headIdx hj a) : A) : Ω) := by
      intro a
      have := h0 (headIdx hj a)
      rw [← blockEquiv_inl] at this
      simp only [Equiv.symm_apply_apply, Sum.elim_inl] at this
      rw [blockEquiv_inl] at this
      exact (sub_eq_zero.1 this).symm
    refine ⟨fun a => - c' a, fun a => ?_, ?_⟩
    · show - c' a ∈ A
      rw [hca]; exact A.neg_mem (c _).2
    · have : ∑ a, (- c' a) • b (headIdx hj a) = - (b (tailIdx hj k) - x k) := by
        rw [← hc']; simp [Finset.sum_neg_distrib]
      rw [this]; abel
  choose C hC hx using key
  exact ⟨Matrix.of fun a k => C k a, fun a k => hC k a, fun k => hx k⟩

variable {b : Fin N → V} {x : Fin (N - j) → V} {C : Matrix (Fin j) (Fin (N - j)) Ω}

include hj in
theorem replaceTail_eq (hx : ∀ k, x k = b (tailIdx hj k) + ∑ a, C a k • b (headIdx hj a)) (q : Fin N) :
    replaceTail hj b x q = ∑ p, blk hj C p q • b p := by
  obtain ⟨u, rfl⟩ := (blockEquiv hj).surjective q
  rw [sum_blocks hj]
  rcases u with a' | k'
  · rw [blockEquiv_inl, replaceTail_head]
    simp [blk_hh, blk_th]
  · rw [blockEquiv_inr, replaceTail_tail, hx]
    simp only [blk_ht, blk_tt, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact add_comm _ _

theorem replaceTail_linearIndependent (hb : LinearIndependent Ω b)
    (hx : ∀ k, x k = b (tailIdx hj k) + ∑ a, C a k • b (headIdx hj a)) :
    LinearIndependent Ω (replaceTail hj b x) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h1 : ∑ p, ((blk hj C).mulVec g) p • b p = 0 := by
    rw [← hg]
    simp only [Matrix.mulVec, dotProduct, Finset.sum_smul, replaceTail_eq hj hx, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]
  have h0 := Fintype.linearIndependent_iff.1 hb _ h1
  have hdet : (blk hj C).det ≠ 0 := by rw [det_blk]; exact one_ne_zero
  have := Matrix.eq_zero_of_mulVec_eq_zero hdet (funext h0)
  intro i
  exact congrFun this i

theorem span_replaceTail (A : Subring Ω) (hC : ∀ a k, C a k ∈ A)
    (hx : ∀ k, x k = b (tailIdx hj k) + ∑ a, C a k • b (headIdx hj a)) :
    Submodule.span A (Set.range (replaceTail hj b x)) = Submodule.span A (Set.range b) := by
  have hs : ∀ (S : Submodule A V) (k : Fin (N - j)), (∀ a, b (headIdx hj a) ∈ S) →
      ∑ a, C a k • b (headIdx hj a) ∈ S := fun S k h =>
    S.sum_mem fun a _ => S.smul_mem (⟨C a k, hC a k⟩ : A) (h a)
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨q, rfl⟩
    obtain ⟨u, rfl⟩ := (blockEquiv hj).surjective q
    have hbm : ∀ p, b p ∈ Submodule.span A (Set.range b) := fun p => Submodule.subset_span ⟨p, rfl⟩
    rcases u with a | k
    · rw [blockEquiv_inl, replaceTail_head]; exact hbm _
    · rw [blockEquiv_inr, replaceTail_tail, hx]
      exact add_mem (hbm _) (hs _ k fun a => hbm _)
  · rw [Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    set S := Submodule.span A (Set.range (replaceTail hj b x)) with hS
    have hm : ∀ q, replaceTail hj b x q ∈ S := fun q => Submodule.subset_span ⟨q, rfl⟩
    have hh : ∀ a, b (headIdx hj a) ∈ S := fun a => by simpa [replaceTail_head] using hm (headIdx hj a)
    obtain ⟨u, rfl⟩ := (blockEquiv hj).surjective p
    rcases u with a | k
    · rw [blockEquiv_inl]; exact hh a
    · rw [blockEquiv_inr]
      have e : b (tailIdx hj k) = x k - ∑ a, C a k • b (headIdx hj a) := by rw [hx]; abel
      rw [e]
      refine sub_mem ?_ (hs S k hh)
      simpa [replaceTail_tail] using hm (tailIdx hj k)

end Frame

end GlobalTheory.CompanionTheory.Ar.SmallGram

namespace GlobalTheory.CompanionTheory.Ar.SmallGram

theorem mem_Vgen_of_mem_V {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {l : Tor.Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
    {S : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω}
    (𝔐 : HodgeCpt Y S y) (s : CMType H ⊕ CMType H) (p : Cpt 𝔐.ξ) {e : 𝔐.Li} (he : e ∈ 𝔐.V s p) : e ∈ 𝔐.Vgen s := by
  obtain ⟨U, hU, b, hb, hf⟩ := (𝔐.vb s : (𝔐.V s).IsVB (labelRk D s) (𝔐.Vgen s)) p (Set.mem_univ p)
  have h2 : 𝔐.V s p = Submodule.span (regAt 𝔐.ξ p) (Set.range b) := (hf p (Set.mem_univ p) hU).2
  have hb' : Submodule.span Ω (Set.range b) = 𝔐.Vgen s := hb
  rw [h2] at he
  rw [← hb']
  have hle : Submodule.span (regAt 𝔐.ξ p) (Set.range b) ≤
      (Submodule.span Ω (Set.range b)).restrictScalars (regAt 𝔐.ξ p) :=
    Submodule.span_le.2 Submodule.subset_span
  exact hle he

theorem quotNormSq_eq_det : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (z : Spec (CommRingCat.of ℂ) ⟶ Or.𝔐.X) (τ : CMType H) (b : Fin Dc.N → W τ) (s : Fin (Dc.N - Dc.j) → Or.𝔐.Li) (h : genPt Or.𝔐.ξ ⤳ centre z) (G : Matrix (Fin Dc.N) (Fin Dc.N) ℂ), Or.𝔐.Interior z → (Lat.comap (fun p => Or.𝔐.V (Or.bg τ) p ⊔ Or.𝔐.V (Or.sm τ) p) (Or.i τ)).IsFrameAt b ⟨centre z, h⟩ → Submodule.span Ω (Set.range (b ∘ headIdx Dc.j_le_N)) = Hd.F τ → (∀ k, s k ∈ Or.𝔐.Vgen (Or.sm τ)) → (∀ k, Or.i τ (b (tailIdx Dc.j_le_N k)) - s k ∈ Or.𝔐.V (Or.bg τ) ⟨centre z, h⟩) → (Or.𝔐.V (Or.sm τ)).IsFrameAt s ⟨centre z, h⟩ → Or.𝔐.M.GramAt Or.𝔐.t.PP.L z (fun k => Or.i τ (b k)) G → G.PosDef → ∃ Γ : Matrix (Fin (Dc.N - Dc.j)) (Fin (Dc.N - Dc.j)) ℂ, Or.𝔐.M.GramAt Or.𝔐.t.PP.L z s Γ ∧ Γ.PosDef ∧ quotNormSq Dc.j_le_N G = Γ.det.re := by
  intro E _ _ _ H D l Xo c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or z τ b s h G hI hb hF hs hd hsf hG hGp
  classical
  haveI : CharZero Ω := algebraRat.charZero Ω
  have hj := Dc.j_le_N
  have hr : ∀ k, ∃ x, Or.i τ x = s k := fun k => by
    have : s k ∈ LinearMap.range (Or.i τ) := by
      rw [Or.i_range]; exact Submodule.mem_sup_right (hs k)
    exact this
  choose x hx using hr
  have h1 : ∀ k, b (tailIdx hj k) - x k ∈ Submodule.span (regAt Or.𝔐.ξ ⟨centre z, h⟩) (Set.range b) := by
    intro k
    rw [← hb.2]
    show Or.i τ (b (tailIdx hj k) - x k) ∈ Or.𝔐.V (Or.bg τ) ⟨centre z, h⟩ ⊔ Or.𝔐.V (Or.sm τ) ⟨centre z, h⟩
    rw [map_sub, hx]
    exact Submodule.mem_sup_left (hd k)
  have h2 : ∀ k, b (tailIdx hj k) - x k ∈ Submodule.span Ω (Set.range (b ∘ headIdx hj)) := by
    intro k
    rw [hF, Or.F_eq, Submodule.mem_comap, map_sub, hx]
    exact mem_Vgen_of_mem_V Or.𝔐 (Or.bg τ) ⟨centre z, h⟩ (hd k)
  obtain ⟨C, hCA, hC⟩ := exists_coeff hj _ hb.1 h1 h2
  have hval : ∀ a k, ∃ r : ℂ, ValAt Or.𝔐.ξ z (C a k) r := by
    intro a k
    obtain ⟨st, hst⟩ := hCA a k
    exact ⟨_, h, st, hst, rfl⟩
  choose Cz hCz using hval
  have hT : ∀ p q, ValAt Or.𝔐.ξ z (blk hj C p q) (blk hj (Matrix.of Cz) p q) := by
    have v0 : ValAt Or.𝔐.ξ z (0 : Ω) (0 : ℂ) := ⟨h, 0, map_zero _, map_zero _⟩
    have v1 : ValAt Or.𝔐.ξ z (1 : Ω) (1 : ℂ) := CxVal.one h
    intro p q
    obtain ⟨u, rfl⟩ := (blockEquiv hj).surjective p
    obtain ⟨u', rfl⟩ := (blockEquiv hj).surjective q
    rcases u with a | k <;> rcases u' with a' | k'
    · simp only [blockEquiv_inl, blk_hh]; split_ifs <;> assumption
    · simp only [blockEquiv_inl, blockEquiv_inr, blk_ht]; exact hCz a k'
    · simp only [blockEquiv_inl, blockEquiv_inr, blk_th]; exact v0
    · simp only [blockEquiv_inr, blk_tt]; split_ifs <;> assumption
  set b' := replaceTail hj b x with hb'
  have hframe : (Lat.comap (fun p => Or.𝔐.V (Or.bg τ) p ⊔ Or.𝔐.V (Or.sm τ) p) (Or.i τ)).IsFrameAt b'
      ⟨centre z, h⟩ :=
    ⟨replaceTail_linearIndependent hj hb.1 hC, by rw [hb.2, hb', span_replaceTail hj _ hCA hC]⟩
  obtain ⟨G', hG', hG'p⟩ := GlobalTheory.T.component_data_hodge_third E H D l Xo c Y II K J Ω W Dc Hd S₀ Or z τ b' h hI hframe
  have hpol := GlobalTheory.T.interior_point_polarised E H D l Xo c Y S₀ Ω K J Dc.y Or.𝔐 z hI
  have hchange : G' = (blk hj (Matrix.of Cz)).conjTranspose * G * blk hj (Matrix.of Cz) :=
    GlobalTheory.T.gram_matrix_two_frames E H D l Xo c Y S₀ Ω K J Dc.y Or.𝔐 z Dc.N (fun k => Or.i τ (b k)) (fun k => Or.i τ (b' k)) G G'
      (blk hj C) (blk hj (Matrix.of Cz)) hpol hG hG'
      (fun q => by rw [hb', replaceTail_eq hj hC, map_sum]; simp only [map_smul]) hT
  obtain ⟨v, hv, hip⟩ := id hG'
  have hhead : ∀ a, Or.i τ (b' (headIdx hj a)) ∈ Or.𝔐.Vgen (Or.bg τ) := by
    intro a
    rw [hb', replaceTail_head]
    have : b (headIdx hj a) ∈ Hd.F τ := by
      rw [← hF]; exact Submodule.subset_span ⟨a, rfl⟩
    rw [Or.F_eq] at this
    exact this
  have htail : ∀ k, Or.i τ (b' (tailIdx hj k)) = s k := fun k => by
    rw [hb', replaceTail_tail, hx]
  have horth : ∀ a k, G' (headIdx hj a) (tailIdx hj k) = 0 := fun a k =>
    GlobalTheory.T.component_data_hodge_fourth E H D l Xo c Y II K J Ω W Dc Hd S₀ Or z τ _ _ _ _ _ hI (hhead a)
      (by show Or.i τ (b' (tailIdx hj k)) ∈ _; rw [htail]; exact hs k) (hv _) (hv _) (hip _ _)
  refine ⟨G'.submatrix (tailIdx hj) (tailIdx hj),
    ⟨fun k => v (tailIdx hj k), fun k => ?_, fun p q => hip _ _⟩, hG'p.submatrix (tailIdx_injective hj), ?_⟩
  · rw [← htail]; exact hv _
  · exact GlobalTheory.T.block_matrix_gram_normal Dc.N Dc.j hj G G' _ _ hGp hchange (blk_hh hj _) (fun k a => blk_th hj _ a k) (blk_tt hj _)
      horth (fun _ _ => rfl)

end GlobalTheory.CompanionTheory.Ar.SmallGram
