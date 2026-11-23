import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.LeviInt

noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
open scoped TensorProduct

section Grp

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem hermForm_base_conj_symm (hσ : ∀ x, σ (σ x) = x) (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin n → E) :
    σ (hE σ J x y) = hE σ J y x := by
  unfold hE Formalism.UG.hform
  simp only [map_sum, map_mul, AlgHom.coe_toRingHom, hσ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hJ a b]
  ring

theorem rational_vector_mem_span {r : ℕ} (Y : Fin r → Fin n → E) (x : Fin n → E)
    (hx : x ∈ Submodule.span E (Set.range Y)) : ratV (F := F) R x ∈ spanR (F := F) R Y Set.univ := by
  induction hx using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨a, rfl⟩ := hu
    exact Submodule.subset_span ⟨a, Set.mem_univ _, rfl⟩
  | zero =>
    have e0 : ratV (F := F) R (0 : Fin n → E) = 0 := funext fun i => map_zero _
    rw [e0]
    exact Submodule.zero_mem _
  | add u w _ _ hu hw =>
    have e0 : ratV (F := F) R (u + w) = ratV (F := F) R u + ratV (F := F) R w :=
      funext fun i => map_add _ _ _
    rw [e0]
    exact Submodule.add_mem _ hu hw
  | smul c u _ hu =>
    have e0 : ratV (F := F) R (c • u) = inclR (F := F) R c • ratV (F := F) R u :=
      funext fun i => by
        first
          | (simp only [ratV, Pi.smul_apply, smul_eq_mul]; exact map_mul _ _ _)
          | (simp [ratV, map_mul]; rfl)
    rw [e0]
    exact Submodule.smul_mem _ _ hu

theorem rational_vector_in_complement {r : ℕ} (P : Frame E n r) (x : Fin n → E) (hx : ∀ a, hE σ J (P.e a) x = 0 ∧ hE σ J (P.f a) x = 0) :
    WbR R σ J P (ratV (F := F) R x) := fun i => ⟨by rw [hermForm_rational_vectors, (hx i).1, map_zero], by rw [hermForm_rational_vectors, (hx i).2, map_zero]⟩

theorem stabilizer_fixes_isotropic_e {r : ℕ} (P : Frame E n r) {h : HA R σ J} (hh : h ∈ Hsub R σ J P) (a : Fin r) :
    lin R σ J h (ratV (F := F) R (P.e a)) = ratV (F := F) R (P.e a) := by
  have hfix : h • ratTup (F := F) R (tupH P) = ratTup (F := F) R (tupH P) := hh
  have h1 : lin R σ J h (ratTup (F := F) R (tupH P) (Fin.castAdd r (Fin.castSucc a))) =
      ratTup (F := F) R (tupH P) (Fin.castAdd r (Fin.castSucc a)) := congrFun hfix _
  have e1 : ratTup (F := F) R (tupH P) (Fin.castAdd r (Fin.castSucc a)) = ratV (F := F) R (P.e a) := by
    funext i
    simp [ratTup, tupH, F0, ratV]
  rwa [e1] at h1

theorem stabilizer_fixes_isotropic_f {r : ℕ} (P : Frame E n r) {h : HA R σ J} (hh : h ∈ Hsub R σ J P) (a : Fin r) :
    lin R σ J h (ratV (F := F) R (P.f a)) = ratV (F := F) R (P.f a) := by
  have hfix : h • ratTup (F := F) R (tupH P) = ratTup (F := F) R (tupH P) := hh
  have h1 : lin R σ J h (ratTup (F := F) R (tupH P) (Fin.natAdd (r + 1) a)) =
      ratTup (F := F) R (tupH P) (Fin.natAdd (r + 1) a) := congrFun hfix _
  have e1 : ratTup (F := F) R (tupH P) (Fin.natAdd (r + 1) a) = ratV (F := F) R (P.f a) := by
    funext i
    simp [ratTup, tupH, F0, ratV]
  rwa [e1] at h1

theorem stabilizer_fixes_span {r : ℕ} (P : Frame E n r) {h : HA R σ J} (hh : h ∈ Hsub R σ J P) (Y : Fin r → Fin n → E)
    (hY : ∀ a, lin R σ J h (ratV (F := F) R (Y a)) = ratV (F := F) R (Y a))
    (y : Fin n → R ⊗[F] E) (hy : y ∈ spanR (F := F) R Y Set.univ) : lin R σ J h y = y := by
  induction hy using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨a, _, rfl⟩ := hu
    exact hY a
  | zero => exact map_zero _
  | add u w _ _ hu hw => rw [map_add, hu, hw]
  | smul c u _ hu => rw [map_smul, hu]

theorem stabilizer_preserves_complement {r : ℕ} (P : Frame E n r) {h : HA R σ J} (hh : h ∈ Hsub R σ J P) {w : Fin n → R ⊗[F] E}
    (hw : WbR R σ J P w) : WbR R σ J P (lin R σ J h w) := fun i => ⟨by rw [← stabilizer_fixes_isotropic_e P hh i, hR_lin]; exact (hw i).1,
    by rw [← stabilizer_fixes_isotropic_f P hh i, hR_lin]; exact (hw i).2⟩

end Grp

section Lat

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E} (v : HeightOneSpectrum (𝓞 F))

theorem localLattice_union (A B : Set (Fin n → E)) :
    latLoc (E := E) v (A ∪ B) = latLoc v A ⊔ latLoc v B := by
  unfold latLoc
  rw [Set.image_union, Submodule.span_union]

theorem localLattice_le_span {r : ℕ} (Y : Fin r → Fin n → E) (A : Set (Fin n → E))
    (hA : ∀ x ∈ A, x ∈ Submodule.span E (Set.range Y)) :
    latLoc (E := E) v A ≤ (spanR (F := F) (Fv F v) Y Set.univ).restrictScalars (v.adicCompletionIntegers F) := by
  unfold latLoc
  rw [Submodule.span_le]
  rintro _ ⟨x, hx, rfl⟩
  exact rational_vector_mem_span (F := F) Y x (hA x hx)

theorem localLattice_le_complement {r : ℕ} (P : Frame E n r) (A : Set (Fin n → E))
    (hA : ∀ w ∈ A, ∀ a, hE σ J (P.e a) w = 0 ∧ hE σ J (P.f a) w = 0) :
    latLoc (E := E) v A ≤ (WbSub (Fv F v) σ J P).restrictScalars (v.adicCompletionIntegers F) := by
  unfold latLoc
  rw [Submodule.span_le]
  rintro _ ⟨x, hx, rfl⟩
  exact rational_vector_in_complement (σ := σ) (J := J) P x (hA x hx)

theorem witt_decomposition_lattice {r : ℕ} (P : Frame E n r) (hee : ∀ a b, hE σ J (P.e a) (P.e b) = 0)
    (hef : ∀ a b, hE σ J (P.e a) (P.f b) = if a = b then 1 else 0)
    (hfe : ∀ a b, hE σ J (P.f a) (P.e b) = if a = b then 1 else 0)
    (A B C : Set (Fin n → E)) (hA : ∀ x ∈ A, x ∈ Submodule.span E (Set.range P.e))
    (hC : ∀ y ∈ C, y ∈ Submodule.span E (Set.range P.f))
    (hB : ∀ w ∈ B, ∀ a, hE σ J (P.e a) w = 0 ∧ hE σ J (P.f a) w = 0)
    {m x w : Fin n → Fv F v ⊗[F] E} (hm : m ∈ latLoc (E := E) v (A ∪ B ∪ C))
    (hx : x ∈ spanR (F := F) (Fv F v) P.e Set.univ) (hw : WbR (Fv F v) σ J P w) (h : m = x + w) :
    w ∈ latLoc (E := E) v B := by
  rw [localLattice_union, localLattice_union] at hm
  obtain ⟨ab, hab, c, hc, rfl⟩ := Submodule.mem_sup.1 hm
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hab
  have ha' := localLattice_le_span v P.e A hA ha
  have hb' := localLattice_le_complement (σ := σ) (J := J) v P B hB hb
  have hc' := localLattice_le_span v P.f C hC hc
  have hwb := witt_decomposition_unique (P := P) (hee := hee) (hef := hef) (hfe := hfe) (hx := hx) (ha := ha')
    (hc := hc') (hw := hw) (hb := hb') (h := h.symm)
  rw [hwb]
  exact hb

theorem lin_mem_localLattice (g : HA (Fv F v) σ J) (A : Set (Fin n → E))
    (hg : ∀ y ∈ A, lin (Fv F v) σ J g (ratV (F := F) (Fv F v) y) ∈ latLoc (E := E) v A)
    (m : Fin n → Fv F v ⊗[F] E) (hm : m ∈ latLoc (E := E) v A) : lin (Fv F v) σ J g m ∈ latLoc (E := E) v A := by
  unfold latLoc at hm ⊢
  induction hm using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨y, hy, rfl⟩ := hu
    exact hg y hy
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add u w _ _ hu hw => rw [map_add]; exact Submodule.add_mem _ hu hw
  | smul c u _ hu =>
    rw [LinearMap.map_smul_of_tower]
    exact Submodule.smul_mem _ _ hu

end Lat

variable {D : D7}

theorem leviIntH : LeviIntH := by
  intro D X w p n h hn hh hK
  classical
  have hstd := FrameW.frameOf_isStd X w
  have hee := hstd.1
  have hef := hstd.2.2.1
  have hσ : ∀ x, X.B.I.cm.sig (X.B.I.cm.sig x) = x := fun x => by simp [FrameW.sig_apply]
  have hJ : ∀ i j, X.B.I.cm.sig (X.B.I.J j i) = X.B.I.J i j := (cmInst_holds X).2.1
  have hfe : ∀ a b, hE X.B.I.cm.sig X.B.I.J ((frameOf X w).f a) ((frameOf X w).e b) = if a = b then 1 else 0 := by
    intro a b
    rw [← hermForm_base_conj_symm hσ hJ, hef b a]
    split_ifs with h1 h2 h2 <;> simp_all
  have had := LatW.adapted X w
  set M := latLoc (E := X.B.I.E) p.1 (LatW.LX X ∪ LatW.LW X ∪ LatW.LY X) with hM
  have hML : latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) = M := (LatW.latLoc_eq X p.1).symm
  have hK' : ∀ x, x ∈ M ↔ lin _ X.B.I.cm.sig X.B.I.J (n * h) x ∈ M := by
    rw [← hML]; exact fun x => hK x
  have hKi : (n * h)⁻¹ ∈ KvSubT X p := (KvSubT X p).inv_mem hK
  have hKi' : ∀ x, x ∈ M ↔ lin _ X.B.I.cm.sig X.B.I.J (n * h)⁻¹ x ∈ M := by
    rw [← hML]; exact fun x => hKi x
  have hgen : ∀ y ∈ LatW.LX X ∪ LatW.LW X ∪ LatW.LY X, ratV (F := X.B.I.F) (Fv X.B.I.F p.1) y ∈ M :=
    fun y hy => Submodule.subset_span ⟨y, hy, rfl⟩
  have hWgen : ∀ y ∈ LatW.LW X, ratV (F := X.B.I.F) (Fv X.B.I.F p.1) y ∈ M :=
    fun y hy => hgen y (Or.inl (Or.inr hy))
  have hLWM : ∀ u, u ∈ latLoc (E := X.B.I.E) p.1 (LatW.LW X) → u ∈ M := by
    intro u hu
    exact (Submodule.span_mono (Set.image_mono (fun y hy => Or.inl (Or.inr hy)))) hu
  have hdec : ∀ {m x w' : Fin X.B.I.n → Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E}, m ∈ M →
      x ∈ spanR (F := X.B.I.F) (Fv X.B.I.F p.1) (frameOf X w).e Set.univ →
      WbR (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w) w' → m = x + w' →
      w' ∈ latLoc (E := X.B.I.E) p.1 (LatW.LW X) := fun hm hx hw he =>
    witt_decomposition_lattice p.1 (frameOf X w) hee hef hfe (LatW.LX X) (LatW.LW X) (LatW.LY X) had.1 had.2.1 had.2.2 hm hx hw he
  have hh' : h⁻¹ ∈ Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w) := inv_mem hh
  have hn' : n⁻¹ ∈ Nsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w) := inv_mem hn

  have hXY : ∀ g ∈ Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w), ∀ y ∈ LatW.LX X ∪ LatW.LY X,
      lin _ X.B.I.cm.sig X.B.I.J g (ratV (F := X.B.I.F) (Fv X.B.I.F p.1) y) = ratV (F := X.B.I.F) (Fv X.B.I.F p.1) y := by
    intro g hg y hy
    rcases hy with hy | hy
    · exact stabilizer_fixes_span (frameOf X w) hg _ (stabilizer_fixes_isotropic_e (frameOf X w) hg) _ (rational_vector_mem_span _ y (had.1 y hy))
    · exact stabilizer_fixes_span (frameOf X w) hg _ (stabilizer_fixes_isotropic_f (frameOf X w) hg) _ (rational_vector_mem_span _ y (had.2.1 y hy))

  have hW1 : ∀ y ∈ LatW.LW X, lin _ X.B.I.cm.sig X.B.I.J h (ratV (F := X.B.I.F) (Fv X.B.I.F p.1) y) ∈ M := by
    intro y hy
    set u := lin _ X.B.I.cm.sig X.B.I.J h (ratV (F := X.B.I.F) (Fv X.B.I.F p.1) y)
    have hu : WbR _ X.B.I.cm.sig X.B.I.J (frameOf X w) u := stabilizer_preserves_complement (frameOf X w) hh (rational_vector_in_complement _ y (had.2.2 y hy))
    have hnu := hn.2 u (fun a => (hu a).1)
    have hm : lin _ X.B.I.cm.sig X.B.I.J n u ∈ M := by
      have := (hK' _).1 (hWgen y hy)
      rwa [lin_mul] at this
    exact hLWM u (hdec hm hnu hu (sub_add_cancel _ _).symm)

  have hW2 : ∀ y ∈ LatW.LW X, lin _ X.B.I.cm.sig X.B.I.J h⁻¹ (ratV (F := X.B.I.F) (Fv X.B.I.F p.1) y) ∈ M := by
    intro y hy
    set y' := ratV (F := X.B.I.F) (Fv X.B.I.F p.1) y
    have hy' : WbR _ X.B.I.cm.sig X.B.I.J (frameOf X w) y' := rational_vector_in_complement _ y (had.2.2 y hy)
    have hx' := hn'.2 y' (fun a => (hy' a).1)
    set x' := lin _ X.B.I.cm.sig X.B.I.J n⁻¹ y' - y'
    have hfix : lin _ X.B.I.cm.sig X.B.I.J h⁻¹ x' = x' :=
      stabilizer_fixes_span (frameOf X w) hh' _ (stabilizer_fixes_isotropic_e (frameOf X w) hh') _ hx'
    have hm : x' + lin _ X.B.I.cm.sig X.B.I.J h⁻¹ y' ∈ M := by
      have := (hKi' _).1 (hWgen y hy)
      rw [mul_inv_rev, lin_mul] at this
      have e : lin _ X.B.I.cm.sig X.B.I.J n⁻¹ y' = y' + x' := by simp [x']
      rw [e, map_add, hfix, add_comm] at this
      exact this
    exact hLWM _ (hdec hm hx' (stabilizer_preserves_complement (frameOf X w) hh' hy') rfl)
  have hall : ∀ g ∈ Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w),
      (∀ y ∈ LatW.LW X, lin _ X.B.I.cm.sig X.B.I.J g (ratV (F := X.B.I.F) (Fv X.B.I.F p.1) y) ∈ M) →
      ∀ m ∈ M, lin _ X.B.I.cm.sig X.B.I.J g m ∈ M := by
    intro g hgH hgW m hm
    refine lin_mem_localLattice p.1 g _ ?_ m hm
    intro y hy
    rcases hy with (hy | hy) | hy
    · rw [hXY g hgH y (Or.inl hy)]; exact hgen y (Or.inl (Or.inl hy))
    · exact hgW y hy
    · rw [hXY g hgH y (Or.inr hy)]; exact hgen y (Or.inr hy)
  show ∀ x, x ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) ↔
    lin _ X.B.I.cm.sig X.B.I.J h x ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))
  rw [hML]
  intro x
  constructor
  · exact hall h hh hW1 x
  · intro hx
    have := hall h⁻¹ hh' hW2 _ hx
    rwa [lin_inv_lin] at this

end MassDataLevelSSteps
