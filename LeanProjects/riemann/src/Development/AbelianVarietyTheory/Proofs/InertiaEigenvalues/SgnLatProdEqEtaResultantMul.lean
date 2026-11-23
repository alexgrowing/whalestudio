import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DltEqZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolyLeftMulBasis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SgnLatSpanBasis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolyDvdPowOfAevalEqZero

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology

namespace GlobalTheory.UnitLemma.SgnProd

theorem val_mul (K : UQ) {x y : K.E} (hx : x ≠ 0) (hy : y ≠ 0) :
    val K.O (x * y) = val K.O x + val K.O y := by
  unfold val
  rw [map_mul, WithZero.log_mul ((Valuation.ne_zero_iff _).2 hx) ((Valuation.ne_zero_iff _).2 hy), neg_add]

theorem eta_mul (K : UQ) {x y : K.E} (hx : x ≠ 0) (hy : y ≠ 0) :
    K.eta (x * y) = K.eta x * K.eta y := by
  unfold UQ.eta
  rw [val_mul K hx hy, zpow_add₀ (by norm_num)]

theorem eta_of_sq_one (K : UQ) {ε : K.E} (h : ε * ε = 1) (a : K.E) : K.eta (ε * a) = K.eta a := by
  have hε : ε ≠ 0 := by rintro rfl; simp at h
  have hv : val K.O ε = 0 := by
    have h1 := val_mul K hε hε
    rw [h] at h1
    have h0 : val K.O (1 : K.E) = 0 := by simp [val]
    omega
  unfold UQ.eta
  by_cases ha : a = 0
  · simp [ha]
  rw [val_mul K hε ha, hv, zero_add]

theorem exists_basis_lat (K : UQ) {V : Type} [AddCommGroup V] [Module K.E V] [Module K.O V]
    [IsScalarTower K.O K.E V] [Module.Finite K.E V] (L : Submodule K.O V) (hfg : L.FG) (hsp : Submodule.span K.E (L : Set V) = ⊤) :
    ∃ e : Module.Basis (Fin (Module.finrank K.E V)) K.E V, Submodule.span K.O (Set.range e) = L := by
  haveI : Submodule.IsLattice K.E L := ⟨hfg, hsp⟩
  let b := Module.Free.chooseBasis K.O L
  let e' := b.extendOfIsLattice K.E
  have hc : Fintype.card (Module.Free.ChooseBasisIndex K.O L) = Module.finrank K.E V :=
    (Module.finrank_eq_card_basis e').symm
  refine ⟨e'.reindex (Fintype.equivFinOfCardEq hc), ?_⟩
  rw [Module.Basis.range_reindex]
  have : Set.range e' = L.subtype '' Set.range b := by
    ext x; simp [e', Set.range_comp]
  rw [this, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_subtype]

theorem exists_smul_mem (K : UQ) {V : Type} [AddCommGroup V] [Module K.E V] [Module K.O V]
    [IsScalarTower K.O K.E V] [Module.Finite K.E V] (L : Submodule K.O V) (hfg : L.FG) (hsp : Submodule.span K.E (L : Set V) = ⊤) (y : V) :
    ∃ s : K.O, s ≠ 0 ∧ s • y ∈ L := by
  obtain ⟨e, he⟩ := exists_basis_lat K L hfg hsp
  obtain ⟨⟨s, hs⟩, hsc⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors K.O) Finset.univ
    (fun i => e.repr y i)
  choose a ha using fun i => hsc i (Finset.mem_univ i)
  refine ⟨s, nonZeroDivisors.ne_zero hs, ?_⟩
  have : s • y = ∑ i, a i • e i := by
    conv_lhs => rw [← e.sum_repr y]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← algebraMap_smul K.E (a i), ha i, ← smul_assoc]
  rw [this, ← he]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end GlobalTheory.UnitLemma.SgnProd

namespace GlobalTheory.UnitLemma.SgnProd

theorem det_trace_ne_zero {K : UQ} (B : InvAlg K) (hsep : B.P.Separable)
    (e : Module.Basis (Fin (Module.finrank K.E B.A)) K.E B.A) :
    (Matrix.of fun k l : Fin (Module.finrank K.E B.A) =>
      Algebra.trace K.E B.A (B.g ^ (k : ℕ) * e l)).det ≠ 0 := by
  intro h0
  obtain ⟨c, hc, hvm⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
  set q : K.E[X] := ∑ k : Fin (Module.finrank K.E B.A), C (c k) * X ^ (k : ℕ) with hq
  have hz : ∀ l, Algebra.trace K.E B.A (aeval B.g q * e l) = 0 := by
    intro l
    have := congrFun hvm l
    simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, Pi.zero_apply] at this
    rw [← this, hq, map_sum, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have ha : aeval B.g (C (c k) * X ^ (k : ℕ)) = c k • B.g ^ (k : ℕ) := by
      rw [← smul_eq_C_mul, map_smul, aeval_X_pow]
    rw [ha, smul_mul_assoc, map_smul, smul_eq_mul]
  have hz' : aeval B.g q = 0 := by
    apply GlobalTheory.UnitLemma.Centraliser.eq_zero_of_trace_mul B hsep
    intro y
    rw [← e.sum_repr y, Finset.mul_sum, map_sum]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [mul_smul_comm, map_smul, hz l, smul_zero]
  have hdvd := GlobalTheory.UnitLemma.Centraliser.P_dvd_of_aeval_eq_zero B hsep q hz'
  have hdeg : q.degree < B.P.degree := by
    have hm : B.P.Monic := LinearMap.charpoly_monic _
    have hn : B.P.natDegree = Module.finrank K.E B.A := LinearMap.charpoly_natDegree _
    rw [degree_eq_natDegree hm.ne_zero, hn]
    exact degree_sum_fin_lt c
  have hq0 : q = 0 := eq_zero_of_dvd_of_degree_lt hdvd hdeg
  apply hc
  funext k
  have := congrArg (fun p : K.E[X] => p.coeff k) hq0
  simp only [hq, finset_sum_coeff, coeff_C_mul_X_pow, coeff_zero] at this
  rw [Finset.sum_eq_single k (fun b _ hb => if_neg (fun h => hb (Fin.ext h.symm))) (by simp)] at this
  simpa using this

theorem trace_mat_toMatrix {E A : Type} [Field E] [CommRing A] [Algebra E A] {ι κ : Type} [Fintype ι]
    [DecidableEq ι] (b : Module.Basis ι E A) (x : κ → A) (f : ι → A) :
    (Matrix.of fun k l => Algebra.trace E A (x k * f l)) =
      (Matrix.of fun k i => Algebra.trace E A (x k * b i)) * b.toMatrix f := by
  ext k l
  rw [Matrix.of_apply, Matrix.mul_apply, ← b.sum_toMatrix_smul_self f l, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_smul_comm, map_smul, smul_eq_mul, Matrix.of_apply, mul_comm]

end GlobalTheory.UnitLemma.SgnProd

namespace GlobalTheory.UnitLemma.SgnProd

open Module

theorem lattice_split (K : UQ) (V₁ V₂ : Type) [AddCommGroup V₁] [Module K.E V₁] [Module K.O V₁]
    [IsScalarTower K.O K.E V₁] [Module.Finite K.E V₁] [AddCommGroup V₂] [Module K.E V₂] [Module K.O V₂]
    [IsScalarTower K.O K.E V₂] [Module.Finite K.E V₂] (M : Submodule K.O (V₁ × V₂)) (hfg : M.FG)
    (hsp : Submodule.span K.E (M : Set (V₁ × V₂)) = ⊤) :
    ∃ (e₁ : Basis (Fin (finrank K.E V₁)) K.E V₁) (e₂ : Basis (Fin (finrank K.E V₂)) K.E V₂)
      (x : Fin (finrank K.E V₂) → V₁ × V₂),
      Submodule.span K.O (Set.range e₁) = M.comap (LinearMap.inl K.O V₁ V₂) ∧
      Submodule.span K.O (Set.range e₂) = M.map (LinearMap.snd K.O V₁ V₂) ∧
      (∀ j, (x j).2 = e₂ j) ∧
      Submodule.span K.O (Set.range (Fin.addCases (fun i => ((e₁ i, 0) : V₁ × V₂)) x)) = M := by
  set M₁ := M.comap (LinearMap.inl K.O V₁ V₂) with hM₁
  set M₂ := M.map (LinearMap.snd K.O V₁ V₂) with hM₂
  have hfg₁ : M₁.FG := by
    haveI : IsNoetherian K.O M := isNoetherian_of_fg_of_noetherian M hfg
    refine Submodule.fg_of_fg_map_injective (LinearMap.inl K.O V₁ V₂) LinearMap.inl_injective ?_
    exact Submodule.FG.of_le_of_isNoetherian (T := M) (Submodule.map_comap_le _ _)
  have hsp₁ : Submodule.span K.E (M₁ : Set V₁) = ⊤ := by
    refine eq_top_iff.2 fun y _ => ?_
    obtain ⟨s, hs0, hs⟩ := exists_smul_mem K M hfg hsp ((y, 0) : V₁ × V₂)
    have hsy : s • y ∈ M₁ := by
      show LinearMap.inl K.O V₁ V₂ (s • y) ∈ M
      simpa [LinearMap.inl_apply, Prod.smul_mk] using hs
    have hs' : algebraMap K.O K.E s ≠ 0 := by
      rwa [ne_eq, (IsFractionRing.injective K.O K.E).eq_iff' (map_zero _)]
    have : y = (algebraMap K.O K.E s)⁻¹ • (s • y) := by
      rw [← algebraMap_smul K.E s y, smul_smul, inv_mul_cancel₀ hs', one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hsy)
  have hfg₂ : M₂.FG := hfg.map _
  have hsp₂ : Submodule.span K.E (M₂ : Set V₂) = ⊤ := by
    have h1 : (M₂ : Set V₂) = (LinearMap.snd K.E V₁ V₂) '' (M : Set (V₁ × V₂)) := by
      rw [hM₂, Submodule.map_coe]; rfl
    rw [h1, Submodule.span_image, hsp, Submodule.map_top, LinearMap.range_eq_top.2 LinearMap.snd_surjective]
  obtain ⟨e₁, he₁⟩ := exists_basis_lat K M₁ hfg₁ hsp₁
  obtain ⟨e₂, he₂⟩ := exists_basis_lat K M₂ hfg₂ hsp₂
  have hlift : ∀ j, ∃ x ∈ M, x.2 = e₂ j := fun j => by
    have : e₂ j ∈ M₂ := he₂ ▸ Submodule.subset_span ⟨j, rfl⟩
    obtain ⟨x, hx, hxe⟩ := Submodule.mem_map.1 this
    exact ⟨x, hx, hxe⟩
  choose x hxM hx2 using hlift
  refine ⟨e₁, e₂, x, he₁, he₂, hx2, le_antisymm ?_ ?_⟩
  · rw [Submodule.span_le]
    rintro _ ⟨l, rfl⟩
    induction l using Fin.addCases with
    | left i =>
      simp only [Fin.addCases_left, SetLike.mem_coe]
      have : e₁ i ∈ M₁ := he₁ ▸ Submodule.subset_span ⟨i, rfl⟩
      exact this
    | right j => simp only [Fin.addCases_right, SetLike.mem_coe]; exact hxM j
  · intro y hy
    have hy2 : y.2 ∈ M₂ := Submodule.mem_map_of_mem hy
    rw [← he₂, Submodule.mem_span_range_iff_exists_fun] at hy2
    obtain ⟨c, hc⟩ := hy2
    set z := y - ∑ j, c j • x j with hz
    have hzM : z ∈ M := M.sub_mem hy (M.sum_mem fun j _ => M.smul_mem _ (hxM j))
    have hz2 : z.2 = 0 := by
      simp only [hz, Prod.snd_sub, Prod.snd_sum, Prod.smul_snd, hx2, hc, sub_self]
    have hz1 : z.1 ∈ M₁ := by
      show LinearMap.inl K.O V₁ V₂ z.1 ∈ M
      have : LinearMap.inl K.O V₁ V₂ z.1 = z := Prod.ext rfl hz2.symm
      rw [this]; exact hzM
    rw [← he₁, Submodule.mem_span_range_iff_exists_fun] at hz1
    obtain ⟨d, hd⟩ := hz1
    have hyz : y = ∑ i, d i • ((e₁ i, 0) : V₁ × V₂) + ∑ j, c j • x j := by
      have : ∑ i, d i • ((e₁ i, 0) : V₁ × V₂) = z := by
        refine Prod.ext ?_ ?_
        · simp [Prod.fst_sum, hd]
        · simp [Prod.snd_sum, hz2]
      rw [this, hz, sub_add_cancel]
    rw [hyz]
    refine Submodule.add_mem _ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_)
      (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_)
    · exact Submodule.subset_span ⟨Fin.castAdd _ i, Fin.addCases_left _⟩
    · exact Submodule.subset_span ⟨Fin.natAdd _ j, Fin.addCases_right _⟩

end GlobalTheory.UnitLemma.SgnProd

namespace GlobalTheory.UnitLemma.SgnProd

open Module

theorem det_trace_lift {E A₁ A₂ : Type} [Field E] [CommRing A₁] [CommRing A₂] [Algebra E A₁] [Algebra E A₂]
    {a b : ℕ} (g : A₁ × A₂) (e₁ : Basis (Fin a) E A₁) (e₂ : Basis (Fin b) E A₂) (x : Fin b → A₁ × A₂)
    (hx : ∀ j, (x j).2 = e₂ j) :
    (Matrix.of fun k l : Fin (a + b) => Algebra.trace E (A₁ × A₂)
      (g ^ (k : ℕ) * Fin.addCases (fun i => ((e₁ i, 0) : A₁ × A₂)) x l)).det =
    (Matrix.of fun k l : Fin (a + b) => Algebra.trace E (A₁ × A₂)
      (g ^ (k : ℕ) * Fin.addCases (fun i => ((e₁ i, 0) : A₁ × A₂)) (fun j => ((0, e₂ j) : A₁ × A₂)) l)).det := by
  classical
  set f : Fin (a + b) → A₁ × A₂ := Fin.addCases (fun i => ((e₁ i, 0) : A₁ × A₂)) x with hf
  let b₀ := (e₁.prod e₂).reindex finSumFinEquiv
  have hb₀ : ∀ l, b₀ l = Fin.addCases (fun i => ((e₁ i, 0) : A₁ × A₂)) (fun j => ((0, e₂ j) : A₁ × A₂)) l := by
    intro l
    induction l using Fin.addCases with
    | left i => simp [b₀]
    | right j => simp [b₀]
  have h := trace_mat_toMatrix b₀ (fun k : Fin (a + b) => g ^ (k : ℕ)) f
  rw [h, Matrix.det_mul]
  simp only [hb₀]
  suffices hU : (b₀.toMatrix f).det = 1 by rw [hU, mul_one]
  have hcc : ∀ i' l', b₀.toMatrix f (Fin.castAdd b i') (Fin.castAdd b l') = if l' = i' then 1 else 0 := by
    intro i' l'
    simp [Basis.toMatrix_apply, b₀, hf, Finsupp.single_apply]
  have hnc : ∀ j' l', b₀.toMatrix f (Fin.natAdd a j') (Fin.castAdd b l') = 0 := by
    intro j' l'
    simp [Basis.toMatrix_apply, b₀, hf]
  have hnn : ∀ j' j, b₀.toMatrix f (Fin.natAdd a j') (Fin.natAdd a j) = if j = j' then 1 else 0 := by
    intro j' j
    simp [Basis.toMatrix_apply, b₀, hf, hx, Finsupp.single_apply]
  have htri : (b₀.toMatrix f).BlockTriangular id := by
    intro i l hli
    simp only [id] at hli
    induction i using Fin.addCases with
    | left i' =>
      induction l using Fin.addCases with
      | left l' =>
        rw [hcc, if_neg]
        rintro rfl
        exact lt_irrefl _ hli
      | right j =>
        exfalso
        rw [Fin.lt_def, Fin.coe_natAdd, Fin.val_castAdd] at hli
        have := i'.2
        omega
    | right j' =>
      induction l using Fin.addCases with
      | left l' => exact hnc j' l'
      | right j =>
        rw [hnn, if_neg]
        rintro rfl
        exact lt_irrefl _ hli
  rw [Matrix.det_of_upperTriangular htri, Fin.prod_univ_add]
  simp [hcc, hnn]

end GlobalTheory.UnitLemma.SgnProd

namespace GlobalTheory.UnitLemma.SgnProd

open Module

theorem sgnLat_prod : ∀ (K : UQ) (B₁ B₂ : InvAlg K), (B₁.P * B₂.P).Separable → ∀ M ∈ (B₁.prod B₂).Lin,
    (B₁.prod B₂).sgnLat M = K.eta (resultant B₁.P B₂.P) *
      B₁.sgnLat (M.comap (LinearMap.inl K.O B₁.A B₂.A)) * B₂.sgnLat (M.map (LinearMap.snd K.O B₁.A B₂.A)) := by
  intro K B₁ B₂ hsep M hM
  obtain ⟨hfg, hsp⟩ := hM.1
  obtain ⟨e₁, e₂, x, he₁, he₂, hx, hspan⟩ := lattice_split K B₁.A B₂.A M hfg hsp
  have hP : (B₁.prod B₂).P = B₁.P * B₂.P := by
    have h1 : LinearMap.mulLeft K.E (B₁.prod B₂).g =
        (LinearMap.mulLeft K.E B₁.g).prodMap (LinearMap.mulLeft K.E B₂.g) := by
      exact LinearMap.ext fun _ => rfl
    have h2 := LinearMap.charpoly_prodMap (LinearMap.mulLeft K.E B₁.g) (LinearMap.mulLeft K.E B₂.g)
    rw [← h1] at h2
    exact h2
  let f : Fin (finrank K.E B₁.A + finrank K.E B₂.A) → B₁.A × B₂.A :=
    Fin.addCases (fun i => ((e₁ i, 0) : B₁.A × B₂.A)) x
  have hcard : Fintype.card (Fin (finrank K.E B₁.A + finrank K.E B₂.A)) = finrank K.E (B₁.A × B₂.A) := by
    simp [Module.finrank_prod]
  have htop : ⊤ ≤ Submodule.span K.E (Set.range f) := by
    rw [← Submodule.span_span_of_tower K.O, hspan]
    exact hsp.ge
  let bf : Basis (Fin (finrank K.E B₁.A + finrank K.E B₂.A)) K.E (B₁.A × B₂.A) :=
    basisOfTopLeSpanOfCardEqFinrank f htop hcard
  have hbf : ⇑bf = f := coe_basisOfTopLeSpanOfCardEqFinrank f htop hcard
  have hN : finrank K.E B₁.A + finrank K.E B₂.A = finrank K.E (B₁.prod B₂).A := by
    rw [← Fintype.card_fin (finrank K.E B₁.A + finrank K.E B₂.A)]
    exact hcard
  let bF : Basis (Fin (finrank K.E (B₁.prod B₂).A)) K.E (B₁.prod B₂).A := bf.reindex (finCongr hN)
  have hrange : Set.range ⇑bF = Set.range f := by
    exact (Basis.range_reindex bf (finCongr hN)).trans (by rw [hbf])
  have hspanF : Submodule.span K.O (Set.range ⇑bF) = M := by
    rw [hrange]
    exact hspan
  have key := SgnBasis.sgnLat_span_basis K (B₁.prod B₂) bF
  rw [hspanF] at key
  rw [key, ← he₁, ← he₂, SgnBasis.sgnLat_span_basis K B₁ e₁, SgnBasis.sgnLat_span_basis K B₂ e₂]
  have hdet : (Matrix.of fun k l : Fin (finrank K.E (B₁.prod B₂).A) =>
      Algebra.trace K.E (B₁.prod B₂).A ((B₁.prod B₂).g ^ (k : ℕ) * bF l)).det =
      (Matrix.of fun k l : Fin (finrank K.E B₁.A + finrank K.E B₂.A) =>
        Algebra.trace K.E (B₁.A × B₂.A) ((B₁.g, B₂.g) ^ (k : ℕ) * f l)).det := by
    rw [← Matrix.det_submatrix_equiv_self (finCongr hN).symm]
    congr 1
    ext k l
    have hbF : bF l = f ((finCongr hN).symm l) := by
      rw [← hbf]
      exact Basis.reindex_apply bf (finCongr hN) l
    simp only [Matrix.submatrix_apply, Matrix.of_apply]
    erw [hbF]
    simp only [finCongr_symm, finCongr_apply, Fin.val_cast]
    rfl
  obtain ⟨ε, hε, hL7⟩ := GlobalTheory.det_trace_pow_prod K.E B₁.A B₂.A B₁.g B₂.g _ _ e₁ e₂ hsep
  have hchain : (Matrix.of fun k l : Fin (finrank K.E (B₁.prod B₂).A) =>
      Algebra.trace K.E (B₁.prod B₂).A ((B₁.prod B₂).g ^ (k : ℕ) * bF l)).det =
      ε * resultant B₁.P B₂.P * (Matrix.of fun k l : Fin (finrank K.E B₁.A) =>
        Algebra.trace K.E B₁.A (B₁.g ^ (k : ℕ) * e₁ l)).det * (Matrix.of fun k l : Fin (finrank K.E B₂.A) =>
        Algebra.trace K.E B₂.A (B₂.g ^ (k : ℕ) * e₂ l)).det :=
    hdet.trans ((det_trace_lift (B₁.g, B₂.g) e₁ e₂ x hx).trans hL7)
  have hne := det_trace_ne_zero (B₁.prod B₂) (by rw [hP]; exact hsep) bF
  rw [hchain] at hne ⊢
  simp only [mul_ne_zero_iff] at hne
  obtain ⟨⟨⟨-, hR⟩, h₁⟩, h₂⟩ := hne
  rw [mul_assoc, mul_assoc, eta_of_sq_one K hε, eta_mul K hR (mul_ne_zero h₁ h₂), eta_mul K h₁ h₂, mul_assoc]

end GlobalTheory.UnitLemma.SgnProd
