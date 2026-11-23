import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuantumDeterminantCommute.Development

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace QmCapCommW

abbrev Pt (k r : ℕ) (i : Fin (r + 1)) (D : Set (Mx k r)) : Type := {g : Mx k r // g ∈ Glev k r i ∩ D}

open Classical in

def ext0 {k r : ℕ} {i : Fin (r + 1)} {D : Set (Mx k r)} {E : Type} [Zero E] (φ : Pt k r i D → E) : Mx k r → E :=
  fun g => if h : g ∈ Glev k r i ∩ D then φ ⟨g, h⟩ else 0

section Core

variable {k r : ℕ} {i : Fin (r + 1)} {D : Set (Mx k r)} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma extension_by_zero_apply {φ : Pt k r i D → E} {g : Mx k r} (hg : g ∈ Glev k r i ∩ D) : ext0 φ g = φ ⟨g, hg⟩ := by
  simp only [ext0, dif_pos hg]

lemma matrixExtendByZero_add (φ ψ : Pt k r i D → E) : ext0 (φ + ψ) = fun h => ext0 φ h + (1 : ℂ) • ext0 ψ h := by
  funext h
  simp only [ext0]
  split_ifs <;> simp

lemma extendByZeroOffSubset_smul_apply (c : ℂ) (φ : Pt k r i D → E) : ext0 (c • φ) = fun h => (fun _ => (0 : E)) h + c • ext0 φ h := by
  funext h
  simp only [ext0]
  split_ifs <;> simp

lemma matrixExtendByZero_zero : ext0 (0 : Pt k r i D → E) = fun _ => 0 := by
  funext h
  simp only [ext0]
  split_ifs <;> simp

lemma smooth_congr (hD : IsOpen D) {f f' : Mx k r → E} (h : ∀ g ∈ Glev k r i ∩ D, f g = f' g)
    (hf : SmoothLev k r i D f) : SmoothLev k r i D f' := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  refine ⟨U ∩ D, F, hU.inter hD, ⟨hgU, hg₀.2⟩, hF.mono Set.inter_subset_left, fun g hg hgl => ?_⟩
  rw [← h g ⟨hgl, hg.2⟩]
  exact hfF g hg.1 hgl

lemma smooth_zero : SmoothLev k r i D (fun _ : Mx k r => (0 : E)) := fun _ _ => ⟨Set.univ, fun _ => 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩

lemma smooth_lin {f f' : Mx k r → E} (hf : SmoothLev k r i D f) (hf' : SmoothLev k r i D f') (c : ℂ) :
    SmoothLev k r i D (fun g => f g + c • f' g) := by
  intro g₀ hg₀
  obtain ⟨U1, F1, hU1, hg1, hF1, hf1⟩ := hf g₀ hg₀
  obtain ⟨U2, F2, hU2, hg2, hF2, hf2⟩ := hf' g₀ hg₀
  refine ⟨U1 ∩ U2, fun g => F1 g + c • F2 g, hU1.inter hU2, ⟨hg1, hg2⟩,
    (hF1.mono Set.inter_subset_left).add ((hF2.mono Set.inter_subset_right).const_smul c),
    fun g hg hgl => ?_⟩
  show f g + c • f' g = F1 g + c • F2 g
  rw [hf1 g hg.1 hgl, hf2 g hg.2 hgl]

variable (k r i D E) in

def SS : Submodule ℂ (Pt k r i D → E) where
  carrier := {φ | SmoothLev k r i D (ext0 φ)}
  add_mem' {φ ψ} hφ hψ := by
    show SmoothLev k r i D (ext0 (φ + ψ))
    rw [matrixExtendByZero_add]; exact smooth_lin hφ hψ 1
  zero_mem' := by
    show SmoothLev k r i D (ext0 (0 : Pt k r i D → E))
    rw [matrixExtendByZero_zero]; exact smooth_zero
  smul_mem' c φ hφ := by
    show SmoothLev k r i D (ext0 (c • φ))
    rw [extendByZeroOffSubset_smul_apply]; exact smooth_lin smooth_zero hφ c

lemma eh_zero (a b : Fin (2 * r + k + 1)) (g : Mx k r) : EH k r a b (fun _ : Mx k r => (0 : E)) g = 0 := by
  simp [EH, EabH, RdV]

def TT (a b : Fin (mdim k r i)) (φ : Pt k r i D → E) : Pt k r i D → E :=
  fun p => EH k r (posL k r i a) (posL k r i b) (ext0 φ) p.1

lemma TT_mem (hP : EabPres) (hD : IsOpen D) {φ : Pt k r i D → E} (hφ : φ ∈ SS k r i D E) (a b : Fin (mdim k r i)) :
    TT a b φ ∈ SS k r i D E := by
  have h1 := (hP E k r 0 i D a b (ext0 φ) (ext0 φ) 0 hD hφ hφ).1
  refine smooth_congr hD (fun g hg => ?_) h1
  exact (extension_by_zero_apply (φ := TT a b φ) hg).symm

lemma TT_add (hP : EabPres) (hD : IsOpen D) {φ ψ : Pt k r i D → E} (hφ : φ ∈ SS k r i D E)
    (hψ : ψ ∈ SS k r i D E) (a b : Fin (mdim k r i)) : TT a b (φ + ψ) = TT a b φ + TT a b ψ := by
  funext p
  have h3 := (hP E k r 0 i D a b (ext0 φ) (ext0 ψ) 1 hD hφ hψ).2.2 p.1 p.2
  show EH k r (posL k r i a) (posL k r i b) (ext0 (φ + ψ)) p.1 =
    EH k r (posL k r i a) (posL k r i b) (ext0 φ) p.1 + EH k r (posL k r i a) (posL k r i b) (ext0 ψ) p.1
  rw [matrixExtendByZero_add, h3, one_smul]

lemma TT_smul (hP : EabPres) (hD : IsOpen D) {φ : Pt k r i D → E} (hφ : φ ∈ SS k r i D E) (c : ℂ)
    (a b : Fin (mdim k r i)) : TT a b (c • φ) = c • TT a b φ := by
  funext p
  have h3 := (hP E k r 0 i D a b (fun _ => (0 : E)) (ext0 φ) c hD smooth_zero hφ).2.2 p.1 p.2
  try dsimp only at h3
  show EH k r (posL k r i a) (posL k r i b) (ext0 (c • φ)) p.1 =
    c • EH k r (posL k r i a) (posL k r i b) (ext0 φ) p.1
  rw [extendByZeroOffSubset_smul_apply]
  try dsimp only
  rw [h3, eh_zero, zero_add]

def EE (hP : EabPres) (hD : IsOpen D) (a b : Fin (mdim k r i)) : Module.End ℂ (SS k r i D E) where
  toFun x := ⟨TT a b x.1, TT_mem hP hD x.2 a b⟩
  map_add' x y := Subtype.ext (TT_add hP hD x.2 y.2 a b)
  map_smul' c x := Subtype.ext (TT_smul hP hD x.2 c a b)

def Rep (F : Mx k r → E) (φ : Pt k r i D → E) : Prop := ∀ g (hg : g ∈ Glev k r i ∩ D), F g = φ ⟨g, hg⟩

lemma EE_rep (hC : CapCongr) (hP : EabPres) (hD : IsOpen D) {F : Mx k r → E} {x : SS k r i D E}
    (h : Rep F x.1) (a b : Fin (mdim k r i)) :
    Rep (EH k r (posL k r i a) (posL k r i b) F) (EE hP hD a b x).1 := by
  unfold Rep at h ⊢
  intro g hg
  show EH k r (posL k r i a) (posL k r i b) F g = EH k r (posL k r i a) (posL k r i b) (ext0 x.1) g
  exact hC E k r i D a b F (ext0 x.1) hD (fun g' hg' => by rw [extension_by_zero_apply hg']; exact h g' hg') g hg

lemma rep_ext (x : SS k r i D E) : Rep (ext0 x.1) x.1 := fun _ hg => extension_by_zero_apply hg

lemma rep_sum {ι : Type*} [Fintype ι] (c : ι → ℂ) {F : ι → Mx k r → E} {x : ι → SS k r i D E}
    (h : ∀ j, Rep (F j) (x j).1) : Rep (fun g => ∑ j, c j • F j g) (∑ j, c j • x j).1 := by
  unfold Rep at h ⊢
  intro g hg
  show ∑ j, c j • F j g = _
  rw [Submodule.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Submodule.coe_smul, Pi.smul_apply, h j g hg]

lemma posL_inj {a b : Fin (mdim k r i)} (e : posL k r i a = posL k r i b) : a = b := by
  have h1 := congrArg Fin.val e
  simp only [posL, Fin.val_mk] at h1
  exact Fin.ext (by omega)

lemma Tm_rep (hC : CapCongr) (hP : EabPres) (hD : IsOpen D) {F : Mx k r → E} {x : SS k r i D E}
    (h : Rep F x.1) (u : ℂ) (a b : Fin (mdim k r i)) :
    Rep (Formalism.QuantumDeterminants.Top (EH k r) u (posL k r i a) (posL k r i b) F) (Tm (EE hP hD) u a b x).1 := by
  have h1 := EE_rep hC hP hD h a b
  unfold Rep at h h1 ⊢
  intro g hg
  by_cases hab : a = b
  · subst hab
    first
      | simp [Formalism.QuantumDeterminants.Top, Formalism.REAL.Tm, Module.algebraMap_end_apply, h g hg, h1 g hg]
      | simp [Formalism.QuantumDeterminants.Top, Tm, Module.algebraMap_end_apply, h g hg, h1 g hg]
  · have hne : posL k r i a ≠ posL k r i b := fun e => hab (posL_inj e)
    first
      | simp [Formalism.QuantumDeterminants.Top, Formalism.REAL.Tm, hab, hne, h1 g hg]
      | simp [Formalism.QuantumDeterminants.Top, Tm, hab, hne, h1 g hg]

lemma foldr_rep (hC : CapCongr) (hP : EabPres) (hD : IsOpen D) (l : List (ℂ × Fin (mdim k r i) × Fin (mdim k r i)))
    {F : Mx k r → E} {x : SS k r i D E} (h : Rep F x.1) :
    Rep ((l.map fun p => Formalism.QuantumDeterminants.Top (EH k r) p.1 (posL k r i p.2.1) (posL k r i p.2.2)).foldr (fun T f => T f) F)
      ((l.map fun p => Tm (EE hP hD) p.1 p.2.1 p.2.2).prod x).1 := by
  induction l with
  | nil => simpa using h
  | cons q l ih =>
    simp only [List.map_cons, List.foldr_cons, List.prod_cons]
    first
      | rw [Module.End.mul_apply]
      | rw [LinearMap.mul_apply]
    exact Tm_rep hC hP hD ih q.1 q.2.1 q.2.2

lemma qminor_apply (hP : EabPres) (hD : IsOpen D) {t : ℕ} (a b : Fin t → Fin (mdim k r i)) (u : ℂ)
    (x : SS k r i D E) :
    qminor (EE hP hD) a b u x = ∑ σ : Equiv.Perm (Fin t), (((Equiv.Perm.sign σ : ℤ) : ℂ)) •
      ((List.ofFn fun k : Fin t => (u - ((k : ℕ) : ℂ), a (σ k), b k)).map
        fun p => Tm (EE hP hD) p.1 p.2.1 p.2.2).prod x := by
  unfold qminor
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Module.End.mul_apply, List.map_ofFn]
  simp [Function.comp_def, Int.cast_smul_eq_zsmul]

lemma qdet_rep (hC : CapCongr) (hP : EabPres) (hD : IsOpen D) (u : ℂ) {F : Mx k r → E} {x : SS k r i D E}
    (h : Rep F x.1) : Rep (capL k r i u F) (qdet (EE hP hD) u x).1 := by
  unfold qdet capL
  rw [qminor_apply]
  unfold qminorOp
  have H := rep_sum (fun σ : Equiv.Perm (Fin (mdim k r i)) => (((Equiv.Perm.sign σ : ℤ) : ℂ)))
    (fun σ => foldr_rep hC hP hD (List.ofFn fun q : Fin (mdim k r i) => (u - ((q : ℕ) : ℂ), σ q, q)) h)
  simp only [List.map_ofFn, Function.comp_def, id] at H ⊢
  intro g hg
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply]
  exact H g hg

lemma EE_gl (hC : CapCongr) (hP : EabPres) (hG : EabGlLev) (hD : IsOpen D) :
    GlRel (EE (E := E) (i := i) hP hD) := by
  unfold GlRel
  unfold EabGlLev at hG
  have loc : ∀ (a b c d : Fin (mdim k r i)) (x : SS k r i D E) (g : Mx k r) (hg : g ∈ Glev k r i ∩ D),
      (EE hP hD a b (EE hP hD c d x)).1 ⟨g, hg⟩ =
        EH k r (posL k r i a) (posL k r i b) (EH k r (posL k r i c) (posL k r i d) (ext0 x.1)) g := by
    intro a b c d x g hg
    show EH k r (posL k r i a) (posL k r i b) (ext0 (TT c d x.1)) g = _
    exact (hC E k r i D a b (EH k r (posL k r i c) (posL k r i d) (ext0 x.1)) (ext0 (TT c d x.1)) hD
      (fun g' hg' => by rw [extension_by_zero_apply hg']; rfl) g hg).symm
  intro a b c d
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext q
  obtain ⟨g, hg⟩ := q
  have key := hG E k r i D a b c d (ext0 x.1) hD x.2 g hg
  change (EE hP hD a b (EE hP hD c d x)).1 ⟨g, hg⟩ - (EE hP hD c d (EE hP hD a b x)).1 ⟨g, hg⟩ = _
  rw [loc a b c d x g hg, loc c d a b x g hg, key]
  split_ifs <;> rfl

end Core

theorem capelli_operator_transfer : CapTransfer := by
  unfold CapTransfer
  intro hC hQ hP hG
  unfold CapCommute
  unfold QdetCommute at hQ
  intro E _ _ k r i D f hD hf g hg u v
  have hmem : (fun q : Pt k r i D => f q.1) ∈ SS k r i D E :=
    smooth_congr hD (fun g' hg' => (extension_by_zero_apply (φ := fun q : Pt k r i D => f q.1) hg').symm) hf
  let x : SS k r i D E := ⟨fun q => f q.1, hmem⟩
  have hx : Rep f x.1 := fun _ _ => rfl
  have h1 := qdet_rep hC hP hD u (qdet_rep hC hP hD v hx)
  have h2 := qdet_rep hC hP hD v (qdet_rep hC hP hD u hx)
  have hcomm := hQ (Module.End ℂ (SS k r i D E)) (mdim k r i) (EE hP hD) (EE_gl hC hP hG hD) u v
  rw [h1 g hg, h2 g hg]
  have := congrArg (fun T => (T x).1 ⟨g, hg⟩) hcomm
  simpa only [Module.End.mul_apply] using this

end QmCapCommW
