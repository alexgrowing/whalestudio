import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.EisensteinChartSplitting.TChartSplit
import Development.WeilBound.ThetaLifts.LatticeBasics.FrameConj
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousRxSymm

noncomputable section

open scoped NNReal Matrix TensorProduct
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open PositivityTheory.RgEis ResidueKilled.Tr
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.StdChart

section GenB

variable {R S : Type} [CommRing R] [CommRing S] {n : ℕ}

theorem rx_bc (f : R →+* S) (g : GL (Fin (n + n)) R) : rx (Formalism.UG.bc f g) = Formalism.UG.bc f (rx g) :=
  Units.ext (by ext r c; rfl)

theorem conj_unitary {ι : Type} [Fintype ι] [DecidableEq ι] {N : Matrix ι ι ℂ} (h : N ∈ Matrix.unitaryGroup ι ℂ) :
    N.map (starRingEnd ℂ) ∈ Matrix.unitaryGroup ι ℂ := by
  rw [Matrix.mem_unitaryGroup_iff'] at *
  have e : star (N.map (starRingEnd ℂ)) * N.map (starRingEnd ℂ) = (star N * N).map (starRingEnd ℂ) := by
    rw [Matrix.map_mul]
    congr 1
  rw [e, h, Matrix.map_one _ (map_zero _) (map_one _)]

theorem sub_unitary (M : Matrix (Fin (n + n)) (Fin (n + n)) ℂ) :
    M ∈ Matrix.unitaryGroup (Fin (n + n)) ℂ ↔
      M.submatrix finSumFinEquiv finSumFinEquiv ∈ Matrix.unitaryGroup (Fin n ⊕ Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
    ← Matrix.submatrix_one_equiv finSumFinEquiv, sub_inj]

end GenB

section Gen3

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem O_iff' (hD : Dict) (σ : E →ₐ[F] E) (χ : (AF F ⊗[F] E)ˣ →* Circle) (z : AF F ⊗[F] E) :
    z ∈ (adCM σ χ).O ↔ ∀ v, compFin F E v z ∈ intLoc F E v :=
  ((hD F E).2.2.2.1 z).trans (GlobalTheory.ThK.Dbl.Frame.mem_intHat z)

theorem fin_iff' (hD : Dict) (σ : E →ₐ[F] E) (χ : (AF F ⊗[F] E)ˣ →* Circle) {N : ℕ} (J : Matrix (Fin N) (Fin N) E)
    (g : GAd σ J) :
    (∀ v, proj σ J v g ∈ stabLoc σ J (stdLattice E N) v) ↔
    ∀ r c, (matHom _ σ J g).1 r c ∈ (adCM σ χ).O ∧ ((matHom _ σ J g)⁻¹ : GL _ _).1 r c ∈ (adCM σ χ).O := by
  have step : ∀ v, proj σ J v g ∈ stabLoc σ J (stdLattice E N) v ↔
      ∀ r c, compFin F E v ((matHom _ σ J g).1 r c) ∈ intLoc F E v ∧
        compFin F E v (((matHom _ σ J g)⁻¹ : GL _ _).1 r c) ∈ intLoc F E v := fun v => by
    rw [mem_stabLoc]
    simp only [mem_latLoc_stdLattice]
    rw [keeps_iff_int (intLoc F E v) (matHom _ σ J (proj σ J v g)), matHom_proj, ← map_inv]
    rfl
  simp only [step, O_iff' hD σ χ]
  exact ⟨fun h r c => ⟨fun v => (h v r c).1, fun v => (h v r c).2⟩, fun h v r c => ⟨(h r c).1 v, (h r c).2 v⟩⟩

theorem inf_iff' {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) {ι : Type} [Fintype ι]
    [DecidableEq ι] (m : GL ι (AF F ⊗[F] E)) :
    Formalism.UG.bc (compInf F E w) m ∈ Formalism.UG.UJ (sigR _ σ) 1 ↔
      m.1.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf τ) ∈ Matrix.unitaryGroup ι ℂ := by
  obtain ⟨M, hM⟩ : ∃ M, M = (Formalism.UG.bc (compInf F E w) m).1 := ⟨_, rfl⟩
  have e0 : m.1.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf τ) = M.map (infEmb τ) := by rw [hM]; rfl
  have e1 : star (M.map (infEmb τ)) = (Formalism.UG.cT (sigR _ σ) M).map (infEmb τ) := by
    ext i j
    exact (infEmb_sigR hCM τ _)
  rw [e0, Matrix.mem_unitaryGroup_iff', e1, ← Matrix.map_mul]
  have e2 : Formalism.UG.bc (compInf F E w) m ∈ Formalism.UG.UJ (sigR _ σ) 1 ↔ Formalism.UG.cT (sigR _ σ) M * 1 * M = 1 := by
    rw [hM]; exact Iff.rfl
  rw [e2, Matrix.mul_one]
  constructor
  · intro h
    rw [h, Matrix.map_one _ (map_zero _) (map_one _)]
  · intro h
    exact Matrix.map_injective (infEmb_bijective hCM τ).1 (h.trans (Matrix.map_one _ (map_zero _) (map_one _)).symm)

theorem arch_iff' (hI : DictInf) {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) (χ : (AF F ⊗[F] E)ˣ →* Circle) {ι : Type} [Fintype ι]
    [DecidableEq ι] (m : GL ι (AF F ⊗[F] E)) :
    (∀ w, Formalism.UG.bc (compInf F E w) m ∈ Formalism.UG.UJ (sigR _ σ) 1) ↔
      ∀ w', m.1.map ((adCM σ χ).φ w') ∈ Matrix.unitaryGroup ι ℂ := by
  obtain ⟨-, hd⟩ := hI F E σ hCM
  let τ : ∀ w : InfinitePlace F, EmbOver E w := fun w => Classical.arbitrary _
  obtain ⟨h1, h2⟩ := hd τ
  have eq1 : ∀ w w', (∀ z, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (τ w) z = (adStd E).φ w' (eqv F E z)) →
      m.1.map ((adCM σ χ).φ w') = m.1.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (τ w)) := fun w w' e => by
    ext i j
    exact (e _).symm
  have eq3 : ∀ w w', (∀ z, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (τ w) z = starRingEnd ℂ ((adStd E).φ w' (eqv F E z))) →
      m.1.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (τ w)) = (m.1.map ((adCM σ χ).φ w')).map (starRingEnd ℂ) := fun w w' e => by
    ext i j
    exact e _
  have eq2 : ∀ w w', (∀ z, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (τ w) z = starRingEnd ℂ ((adStd E).φ w' (eqv F E z))) →
      m.1.map ((adCM σ χ).φ w') = (m.1.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (τ w))).map (starRingEnd ℂ) := fun w w' e => by
    rw [eq3 w w' e]
    ext i j
    simp
  constructor
  · intro h w'
    obtain ⟨w, hw⟩ := h2 w'
    have hu := (inf_iff' hCM (τ w) m).1 (h w)
    rcases hw with e | e
    · rwa [eq1 w w' e]
    · rw [eq2 w w' e]
      exact conj_unitary hu
  · intro h w
    obtain ⟨w', hw⟩ := h1 w
    refine (inf_iff' hCM (τ w) m).2 ?_
    rcases hw with e | e
    · rw [← eq1 w w' e]
      exact h w'
    · rw [eq3 w w' e]
      exact conj_unitary (h w')

theorem level_iff (hD : Dict) (hI : DictInf) {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) (χ : (AF F ⊗[F] E)ˣ →* Circle) {N : ℕ}
    (J : Matrix (Fin N) (Fin N) E) (g : GAd σ J) :
    g ∈ levelAll σ J (stdLattice E N) 1 ↔ matHom _ σ J g ∈ (adCM σ χ).kGL (Fin N) := by
  have a : ∀ w, projArch σ J w g ∈ stabArch σ J w (Formalism.UG.bc (compInf F E w) 1) ↔
      Formalism.UG.bc (compInf F E w) (matHom _ σ J g) ∈ Formalism.UG.UJ (sigR _ σ) 1 := fun w => by
    rw [mem_stabArch, map_one, inv_one, one_mul, mul_one, matHom_projArch]
  rw [mem_levelAll]
  simp only [a]
  rw [fin_iff' hD σ χ J g, arch_iff' hI hCM χ]
  exact Iff.rfl

theorem mem_ratPts_of (σ : E →ₐ[F] E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E) (g : GAd σ J) (γ : GL (Fin N) E)
    (e : Formalism.UG.bc (inclR (F := F) (E := E) (AF F)) γ = matHom _ σ J g) : g ∈ ratPts σ J := by
  refine ⟨γ, ?_, e⟩
  have hg : Formalism.UG.cT (sigR (AF F) σ) (matHom _ σ J g).1 * JR (AF F) J * (matHom _ σ J g).1 = JR (AF F) J :=
    Subtype.prop (p := (· ∈ HR _ _ _)) g
  rw [← e] at hg
  haveI : Nontrivial (AF F) := ⟨⟨0, 1, fun e => by
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    exact zero_ne_one ((map_zero (evInf F w)).symm.trans ((congrArg (evInf F w) e).trans (map_one _)))⟩⟩
  have inj : Function.Injective (inclR (F := F) (E := E) (AF F)) := RingHom.injective _
  refine Matrix.map_injective inj ?_
  have e2 : (Formalism.UG.cT (σ : E →+* E) γ.1).map (inclR (F := F) (E := E) (AF F)) =
      Formalism.UG.cT (sigR (AF F) σ) (Formalism.UG.bc (inclR (F := F) (E := E) (AF F)) γ).1 := rfl
  change Matrix.map (Formalism.UG.cT (σ : E →+* E) γ.1 * J * γ.1) (inclR (F := F) (E := E) (AF F)) = Matrix.map J _
  rw [Matrix.map_mul, Matrix.map_mul, e2]
  exact hg

end Gen3

section Gen4

variable {E R : Type} [Field E] [CommRing R] {n : ℕ}

theorem rx_kGL (A : Ad E R) (m : GL (Fin (n + n)) R) : rx m ∈ A.kGL (Fin n ⊕ Fin n) ↔ m ∈ A.kGL (Fin (n + n)) := by
  change ((∀ r c, (rx m).1 r c ∈ A.O ∧ ((rx m)⁻¹ : GL _ _).1 r c ∈ A.O) ∧
      ∀ w, (rx m).1.map (A.φ w) ∈ Matrix.unitaryGroup _ ℂ) ↔
    ((∀ r c, m.1 r c ∈ A.O ∧ (m⁻¹ : GL _ _).1 r c ∈ A.O) ∧ ∀ w, m.1.map (A.φ w) ∈ Matrix.unitaryGroup _ ℂ)
  refine and_congr ?_ (forall_congr' fun w => ?_)
  · rw [rx_inv_val, rx_val]
    constructor
    · intro h r c
      have := h (finSumFinEquiv.symm r) (finSumFinEquiv.symm c)
      simpa only [Matrix.submatrix_apply, Equiv.apply_symm_apply] using this
    · intro h r c
      exact h _ _
  · have e : (rx m).1.map (A.φ w) = (m.1.map (A.φ w)).submatrix finSumFinEquiv finSumFinEquiv := rfl
    rw [e]
    exact (sub_unitary (m.1.map (A.φ w))).symm

end Gen4
section Main

variable (D : D7) {n : ℕ} (χ : (AE D)ˣ →* Circle)

theorem mem_upperHalf (x : Fin (n + n) → AE D) :
    x ∈ GlobalTheory.StdUnn.upperHalf D n ↔ ∀ i : Fin n, x (finSumFinEquiv (Sum.inr i)) = 0 := by
  rw [GlobalTheory.StdUnn.upperHalf, LinearMap.mem_ker]
  exact funext_iff

theorem low_zero {g : GL (Fin (n + n)) (AE D)} (h : g ∈ Formalism.UG.stabGL (GlobalTheory.StdUnn.upperHalf D n)) (i j : Fin n) :
    g.1 (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)) = 0 := by
  have h1 : (Pi.single (finSumFinEquiv (Sum.inl j)) 1 : Fin (n + n) → AE D) ∈ GlobalTheory.StdUnn.upperHalf D n :=
    (mem_upperHalf D _).2 fun i => Pi.single_eq_of_ne (fun e => by simpa using finSumFinEquiv.injective e) _
  have := (mem_upperHalf D _).1 ((h _).1 h1) i
  simpa using this

theorem keep_of_low {M : Matrix (Fin (n + n)) (Fin (n + n)) (AE D)}
    (h : ∀ i j : Fin n, M (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)) = 0) {x : Fin (n + n) → AE D}
    (hx : x ∈ GlobalTheory.StdUnn.upperHalf D n) : M *ᵥ x ∈ GlobalTheory.StdUnn.upperHalf D n := by
  refine (mem_upperHalf D _).2 fun i => ?_
  have hx' := (mem_upperHalf D _).1 hx
  have a : ∀ j, M (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)) * x (finSumFinEquiv (Sum.inl j)) = 0 :=
    fun j => by rw [h, zero_mul]
  have b : ∀ j, M (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inr j)) * x (finSumFinEquiv (Sum.inr j)) = 0 :=
    fun j => by rw [hx', mul_zero]
  rw [Matrix.mulVec, dotProduct, ← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [a, b, Finset.sum_const_zero, add_zero]

theorem stab_iff (g : GL (Fin (n + n)) (AE D)) :
    g ∈ Formalism.UG.stabGL (GlobalTheory.StdUnn.upperHalf D n) ↔
      rx g ∈ stab (AE D) (Sum.inl '' (Set.univ : Set (Fin n))) := by
  constructor
  · intro h r hr c hc
    obtain ⟨j, -, rfl⟩ := hc
    rcases r with a | i
    · exact absurd ⟨a, trivial, rfl⟩ hr
    · refine ⟨low_zero D h i j, ?_⟩
      rw [rx_inv_val]
      exact low_zero D (inv_mem h) i j
  · intro h
    have hr : ∀ i : Fin n, (Sum.inr i : Fin n ⊕ Fin n) ∉ Sum.inl '' (Set.univ : Set (Fin n)) := fun i => by simp
    have hc : ∀ j : Fin n, (Sum.inl j : Fin n ⊕ Fin n) ∈ Sum.inl '' (Set.univ : Set (Fin n)) := fun j => ⟨j, trivial, rfl⟩
    have h1 : ∀ i j : Fin n, g.1 (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)) = 0 :=
      fun i j => (h _ (hr i) _ (hc j)).1
    have h2 : ∀ i j : Fin n, (g⁻¹ : GL (Fin (n + n)) (AE D)).1 (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)) = 0 :=
      fun i j => by
        have := (h _ (hr i) _ (hc j)).2
        rw [rx_inv_val] at this
        exact this
    intro x
    refine ⟨keep_of_low D h1, fun hx => ?_⟩
    have := keep_of_low D h2 hx
    rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this

theorem mem_P (g : GlobalTheory.StdUnn.G D n) :
    g ∈ GlobalTheory.StdUnn.P D n ↔ Psi D χ n g ∈ (adCM D.sp.cm.sig χ).uQ (-1) (Set.univ : Set (Fin n)) :=
  stab_iff D _

theorem bdet_eq (g : GL (Fin (n + n)) (AE D)) (a : GL (Fin n) (AE D)) (h : GlobalTheory.StdUnn.blkA g.1 = a.1) :
    bdet (Sum.inl '' (Set.univ : Set (Fin n))) (rx g) = Matrix.GeneralLinearGroup.det a := by
  let e' : Fin n ≃ (Sum.inl '' (Set.univ : Set (Fin n)) : Set (Fin n ⊕ Fin n)) :=
    Equiv.ofBijective (fun i => ⟨Sum.inl i, i, trivial, rfl⟩)
      ⟨fun i j e => Sum.inl_injective (congrArg Subtype.val e), fun ⟨_, i, _, e⟩ => ⟨i, Subtype.ext e⟩⟩
  have hd : ∀ (_ : DecidableEq (Sum.inl '' (Set.univ : Set (Fin n)) : Set (Fin n ⊕ Fin n)))
      (_ : Fintype (Sum.inl '' (Set.univ : Set (Fin n)) : Set (Fin n ⊕ Fin n))),
      ((rx g).1.submatrix (Subtype.val : (Sum.inl '' (Set.univ : Set (Fin n)) : Set (Fin n ⊕ Fin n)) → _) Subtype.val).det = a.1.det := by
    intro _ _
    rw [← Matrix.det_submatrix_equiv_self e', ← h]
    rfl
  rw [bdet]
  split_ifs with hu
  · exact Units.ext (hu.unit_spec.trans (hd _ _))
  · exact absurd ((hd _ _).symm ▸ (Matrix.GeneralLinearGroup.det a).isUnit) hu

end Main

section Main2

variable (D : D7) {n : ℕ} (χ : (AE D)ˣ →* Circle)

theorem mem_GF (g : GlobalTheory.StdUnn.G D n) :
    g ∈ GlobalTheory.StdUnn.GF D n ↔ Psi D χ n g ∈ (adCM D.sp.cm.sig χ).uΓ (-1) (Fin n) := by
  constructor
  · rintro ⟨γ, hγ, e⟩
    refine ⟨rx γ, ?_⟩
    have e' : Formalism.UG.bc (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F)) γ = matHom _ D.sp.cm.sig (GlobalTheory.StdUnn.Jst D n) g := e
    change Formalism.UG.bc (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F)) (rx γ) = (Psi D χ n g).1
    rw [Psi_val, ← e', rx_bc]
  · rintro ⟨γ', e⟩
    refine mem_ratPts_of _ _ g (rx.symm γ') ?_
    apply rx.injective
    rw [rx_bc, MulEquiv.apply_symm_apply]
    exact e

theorem mem_K (hD : Dict) (hI : DictInf) (g : GlobalTheory.StdUnn.G D n) :
    g ∈ GlobalTheory.StdUnn.K D n ↔ Psi D χ n g ∈ (adCM D.sp.cm.sig χ).uK (-1) (Fin n) :=
  (level_iff hD hI (isCMExt_host D) χ (GlobalTheory.StdUnn.Jst D n) g).trans (rx_kGL _ _).symm

end Main2

end GlobalTheory.CompanionTheory.StdChart

end
