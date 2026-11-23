import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegFlagged
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticCurveSubbundleCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagBundleProjVectorBundle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsArithVarOfInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleBaseChangeArithVariety
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharZeroResidueFieldGenericPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SwapIdentityFromRegularBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagBundlePullFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt

set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.VB GlobalTheory.CovTest GlobalTheory.FlagChain

namespace GlobalTheory.TwoLat.Gen

section Flags

variable {X Y Z : Scheme.{0}} {E E' F F' : X.Modules} {r : ℕ}

theorem compat_ofIso {u : E ⟶ E'} {v : F ⟶ F'} {a : Vert.Flag E r} {b : Vert.Flag E' r} (h : Compat u a b)
    (e : E ≅ F) (e' : E' ≅ F') (w : e.hom ≫ v = u ≫ e'.hom) : Compat v (a.ofIso e) (b.ofIso e') := fun i => by
  obtain ⟨t, ht⟩ := h i
  refine ⟨t, ?_⟩
  change t ≫ b.ι i ≫ e'.hom = (a.ι i ≫ e.hom) ≫ v
  rw [← Category.assoc, ht, Category.assoc, Category.assoc, w]

theorem compat_of_le {u : E ⟶ E'} {a a' : Vert.Flag E r} {b : Vert.Flag E' r} (h : Compat u a b)
    (l : ∀ i, Le (a'.ι i) (a.ι i)) : Compat u a' b := fun i => by
  obtain ⟨t, ht⟩ := h i
  obtain ⟨s, hs⟩ := l i
  exact ⟨s ≫ t, by rw [Category.assoc, ht, ← Category.assoc, hs]⟩

def Flagged (u : E ⟶ E') (r : ℕ) : Prop := ∃ (m : Vert.Flag E r) (m' : Vert.Flag E' r), Compat u m m'

theorem Flagged.pull {u : E ⟶ E'} (h : Flagged u r) (ρ : Y ⟶ X) : Flagged ((Scheme.Modules.pullback ρ).map u) r :=
  have ⟨_, _, h⟩ := h
  ⟨_, _, h.pull ρ⟩

theorem Flagged.comp {u : E ⟶ E'} {ρ : Y ⟶ X} {τ : Z ⟶ Y}
    (h : Flagged ((Scheme.Modules.pullback τ).map ((Scheme.Modules.pullback ρ).map u)) r) :
    Flagged ((Scheme.Modules.pullback (τ ≫ ρ)).map u) r :=
  have ⟨_, _, h⟩ := h
  ⟨_, _, compat_ofIso h ((Scheme.Modules.pullbackComp τ ρ).app E) ((Scheme.Modules.pullbackComp τ ρ).app E')
    ((Scheme.Modules.pullbackComp τ ρ).hom.naturality u).symm⟩

theorem flagged_zero (u : E ⟶ E') (hE : IsVB E 0) (hE' : IsVB E' 0) : Flagged u 0 := by
  let z {G : X.Modules} (h : IsVB G 0) : Vert.Flag G 0 :=
    ⟨fun _ => G, fun _ => 𝟙 G, fun _ => VB.isSubbundle_of_isIso (𝟙 G), fun i => by rw [Fin.val_eq_zero i]; exact h,
      fun i => i.elim0, fun i => i.elim0, inferInstance⟩
  exact ⟨z hE, z hE', fun _ => ⟨u, (Category.comp_id _).trans (Category.id_comp _).symm⟩⟩

theorem Flagged.extend {u : E ⟶ E'} {v : F ⟶ F'} {i : F ⟶ E} {i' : F' ⟶ E'} (h : Flagged v r) (hi : IsSubbundle i)
    (hi' : IsSubbundle i') (hE : IsVB E (r + 1)) (hE' : IsVB E' (r + 1)) (w : v ≫ i' = i ≫ u) : Flagged u (r + 1) := by
  obtain ⟨m, m', h⟩ := h
  obtain ⟨a, ha⟩ := Vert.Flag.exists_extend hi hE m
  obtain ⟨a', ha'⟩ := Vert.Flag.exists_extend hi' hE' m'
  refine ⟨a, a', fun j => ?_⟩
  induction j using Fin.lastCases with
  | last => exact ⟨a.ι _ ≫ u ≫ inv (a'.ι _), by simp⟩
  | cast j =>
    obtain ⟨e, he⟩ := ha j
    obtain ⟨e', he'⟩ := ha' j
    obtain ⟨t, ht⟩ := h j
    refine ⟨e.hom ≫ t ≫ e'.inv, ?_⟩
    rw [← he, ← he']
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [reassoc_of% ht, w]

end Flags

section Covers

variable {k : Type} [CommRing k] {D : ℕ}

theorem exists_cov_killed {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} (hX : IsArithVar p D) {E L : X.Modules} {n : ℕ}
    (φ : E ⟶ L) (hE : IsVB E (n + 1)) (hL : IsVB L 1) : ∃ (Y : Scheme.{0}) (ρ : Y ⟶ X) (_ : IsIntegral Y), IsCov p D ρ ∧
      ∃ (K : Y.Modules) (i : K ⟶ (Scheme.Modules.pullback ρ).obj E), IsSubbundle i ∧ IsVB K n ∧
        i ≫ (Scheme.Modules.pullback ρ).map φ = 0 := by
  by_cases hφ : φ = 0
  · obtain ⟨Y, ρ, K, i, h₁, h₂, h₃, h₄⟩ := CorankOne.exists_modification_subbundle hX hE
    have := h₁.isIntegral
    exact ⟨Y, ρ, this, ⟨h₁, h₂⟩, K, i, h₃, h₄, by rw [hφ, Functor.map_zero, comp_zero]⟩
  · obtain ⟨Y, ρ, _, h₁, h₂, h₃⟩ := exists_cov_kernel hX φ hE hL hφ
    exact ⟨Y, ρ, inferInstance, h₁, _, _, h₂, h₃, kernel.condition _⟩

theorem exists_cov_flagged (n : ℕ) : ∀ {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}, IsArithVar p D →
    ∀ {E E' : X.Modules} (u : E ⟶ E'), IsVB E n → IsVB E' n →
      ∃ (Y : Scheme.{0}) (ρ : Y ⟶ X) (_ : IsIntegral Y), IsCov p D ρ ∧
        Flagged ((Scheme.Modules.pullback ρ).map u) n := by
  induction n with
  | zero =>
    intro X _ p hX E E' u hE hE'
    exact ⟨X, 𝟙 X, inferInstance, .id hX, flagged_zero _ (hE.pullback _) (hE'.pullback _)⟩
  | succ n ih =>
    intro X _ p hX E E' u hE hE'
    obtain ⟨X₁, ρ₁, K', i', a₁, a₂, hi', hK'⟩ := CorankOne.exists_modification_subbundle hX hE'
    have := a₁.isIntegral
    have h₁ : IsCov p D ρ₁ := ⟨a₁, a₂⟩
    obtain ⟨s, hs, hL⟩ := isVB_cokernel hi' hK' (hE'.pullback ρ₁)
    obtain rfl : s = 1 := by omega
    obtain ⟨X₂, ρ₂, _, h₂, K, i, hi, hK, h0⟩ := exists_cov_killed h₁.1
      ((Scheme.Modules.pullback ρ₁).map u ≫ cokernel.π i') (hE.pullback ρ₁) hL
    have hi₂ := SubPull.isSubbundle_pullback _ _ ρ₂ _ _ i' _ hK' hi'
    have := hi₂.mono
    have h₃ : (i ≫ (Scheme.Modules.pullback ρ₂).map ((Scheme.Modules.pullback ρ₁).map u)) ≫
        cokernel.π ((Scheme.Modules.pullback ρ₂).map i') = 0 := by
      rw [← cancel_mono (cokernelComparison i' (Scheme.Modules.pullback ρ₂)), Category.assoc,
        π_comp_cokernelComparison, Category.assoc, ← Functor.map_comp, h0, zero_comp]
    obtain ⟨X₃, ρ₃, _, h₄, hf⟩ := ih h₂.1 (Abelian.monoLift _ _ h₃) hK (hK'.pullback ρ₂)
    refine ⟨X₃, (ρ₃ ≫ ρ₂) ≫ ρ₁, inferInstance, h₁.comp (h₂.comp h₄), Flagged.comp (Flagged.comp ?_)⟩
    refine hf.extend (SubPull.isSubbundle_pullback _ _ ρ₃ _ _ i _ hK hi)
      (SubPull.isSubbundle_pullback _ _ ρ₃ _ _ _ _ (hK'.pullback ρ₂) hi₂)
      (((hE.pullback ρ₁).pullback ρ₂).pullback ρ₃) (((hE'.pullback ρ₁).pullback ρ₂).pullback ρ₃) ?_
    rw [← Functor.map_comp, ← Functor.map_comp, Abelian.monoLift_comp]

theorem exists_cov_regFlagged (hR : Published.RegularAlteration) {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
    (hX : IsArithVar p D) {ι : Type} [Fintype ι] {E E' : ι → X.Modules} {r : ι → ℕ} (u : ∀ a, E a ⟶ E' a)
    (hE : ∀ a, IsVB (E a) (r a)) (hE' : ∀ a, IsVB (E' a) (r a)) :
    ∃ (Y : Scheme.{0}) (ρ : Y ⟶ X) (_ : IsIntegral Y), IsCov p D ρ ∧
      RegFlagged Y ι (fun a => (Scheme.Modules.pullback ρ).obj (E a)) (fun a => (Scheme.Modules.pullback ρ).obj (E' a)) r
        fun a => (Scheme.Modules.pullback ρ).map (u a) := by
  classical
  have key (s : Finset ι) : ∃ (Y : Scheme.{0}) (ρ : Y ⟶ X) (_ : IsIntegral Y), IsCov p D ρ ∧
      ∀ a ∈ s, Flagged ((Scheme.Modules.pullback ρ).map (u a)) (r a) := by
    induction s using Finset.induction_on with
    | empty => exact ⟨X, 𝟙 X, inferInstance, .id hX, by simp⟩
    | insert a s _ ih =>
      obtain ⟨Y, ρ, _, h₁, h₂⟩ := ih
      obtain ⟨Z, τ, _, h₃, h₄⟩ := exists_cov_flagged (r a) h₁.1 ((Scheme.Modules.pullback ρ).map (u a))
        ((hE a).pullback ρ) ((hE' a).pullback ρ)
      refine ⟨Z, τ ≫ ρ, inferInstance, h₁.comp h₃, fun b hb => ?_⟩
      rcases Finset.mem_insert.1 hb with rfl | hb
      · exact h₄.comp
      · exact ((h₂ b hb).pull τ).comp
  obtain ⟨Y, ρ, _, h₁, h₂⟩ := key Finset.univ
  obtain ⟨Z, _, τ, a₁, a₂, a₃, a₄⟩ := AlterationOrder.regularAlteration_order hR k Y (ρ ≫ p) D h₁.1
  exact ⟨Z, τ ≫ ρ, inferInstance, h₁.comp ⟨a₁, a₃, a₄⟩, a₂, fun a => ((h₂ a (Finset.mem_univ a)).pull τ).comp⟩

theorem isSeparated_str {X : Scheme.{0}} {p : X ⟶ Sp k} (hp : IsArithVar p D) : IsSeparated p := by
  obtain ⟨N, j, _, e⟩ := hp.isProjOver
  have := isProper_str k N
  rw [← e]
  infer_instance

theorem isProjOver_pullback_fst {X Y₁ Y₂ : Scheme.{0}} {p : X ⟶ Sp k} (hp : IsArithVar p D) {f : Y₁ ⟶ X} {g : Y₂ ⟶ X}
    (hf : IsProjOver (f ≫ p)) (hg : IsProjOver (g ≫ p)) : IsProjOver (pullback.fst f g ≫ f ≫ p) := by
  have := isSeparated_str hp
  have h := ProjSpace.isProjOver_comp_of_isClosedImmersion (pullback.mapDesc f g p)
    (ProjSpace.isProjOver_pullback hf hg)
  rwa [pullback.lift_fst_assoc, Category.comp_id] at h

theorem exists_common_cov {X Y₁ Y₂ : Scheme.{0}} [IsIntegral X] [IsIntegral Y₁] [IsIntegral Y₂] {p : X ⟶ Sp k}
    (hp : IsArithVar p D) {f : Y₁ ⟶ X} {g : Y₂ ⟶ X} (hf : IsCov p D f) (hg : IsCov p D g) :
    ∃ (Z : Scheme.{0}) (_ : IsIntegral Z) (t₁ : Z ⟶ Y₁) (t₂ : Z ⟶ Y₂), t₁ ≫ f = t₂ ≫ g ∧
      IsCov (f ≫ p) D t₁ ∧ IsCov (g ≫ p) D t₂ := by
  obtain ⟨z, z₁, z₂, d₁, d₂⟩ := GlobalTheory.T.pullback_point_residue_nonzero X Y₁ Y₂ f g _ _ (hf.2.1.trans hg.2.1.symm) hf.2.2 hg.2.2
  obtain ⟨Z, i, _, _, hi⟩ := exists_isClosedImmersion_genericPoint z
  have hZ : IsProjOver ((i ≫ pullback.fst f g) ≫ f ≫ p) := by
    rw [Category.assoc]
    exact ProjSpace.isProjOver_comp_of_isClosedImmersion i
      (isProjOver_pullback_fst hp hf.1.isProjOver hg.1.isProjOver)
  have g₁ : (i ≫ pullback.fst f g) (genericPoint Z) = genericPoint Y₁ := by
    simp [hi, z₁]
  have g₂ : (i ≫ pullback.snd f g) (genericPoint Z) = genericPoint Y₂ := by
    simp [hi, z₂]
  have r₁ : (i ≫ pullback.fst f g).residueDegree (genericPoint Z) ≠ 0 := by
    rw [CurveDegreesCompare.residueDegree_comp, GlobalTheory.Published.residueDegree_of_isClosedImmersion i, mul_one, hi]
    exact d₁
  have r₂ : (i ≫ pullback.snd f g).residueDegree (genericPoint Z) ≠ 0 := by
    rw [CurveDegreesCompare.residueDegree_comp, GlobalTheory.Published.residueDegree_of_isClosedImmersion i, mul_one, hi]
    exact d₂
  have hfl : Flat (((i ≫ pullback.fst f g) ≫ f ≫ p) ≫ spMap (Int.castRingHom k)) := by
    rw [flat_int_iff_charZero]
    have c₂ := charZero_residueField_genericPoint Y₁ hf.1.charZero
    have c₃ : CharZero (Z.residueField (genericPoint Z)) := by
      have : ∀ y : Y₁, y = genericPoint Y₁ → CharZero (Y₁.residueField y) := by
        rintro _ rfl; exact c₂
      have := this _ g₁
      exact (RingHom.charZero_iff (Scheme.Hom.residueFieldMap _ _).hom.injective).1 this
    exact (Z.Γevaluation (genericPoint Z)).hom.charZero
  have hq : IsArithVar ((i ≫ pullback.fst f g) ≫ f ≫ p) D :=
    ⟨hp.isDomain, hp.finite, inferInstance, hZ, hfl,
      GlobalTheory.T.dimension_of_dominant_flat_cover k Y₁ Z (f ≫ p) _ D hf.1 hZ hfl (i ≫ pullback.fst f g) rfl g₁ r₁⟩
  have e : (i ≫ pullback.fst f g) ≫ f = (i ≫ pullback.snd f g) ≫ g := by
    simp [pullback.condition]
  refine ⟨Z, inferInstance, _, _, e, ⟨hq, g₁, r₁⟩, ?_, g₂, r₂⟩
  rwa [← Category.assoc, ← e, Category.assoc]

theorem isCov_pullback_fst {B B₁ Y : Scheme.{0}} [IsIntegral B] [IsIntegral B₁] [IsIntegral Y] {q : B ⟶ Sp k} {π : Y ⟶ B}
    {g : B₁ ⟶ B} {d : ℕ} (hq : IsArithVar q d) (hp : IsArithVar (π ≫ q) D) (hg : IsCov q d g) {ι : Type} [Fintype ι]
    {E : ι → B.Modules} {r : ι → ℕ} (hE : ∀ a, IsVB (E a) (r a))
    {fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)} (hfl : IsFlagBundle π E r fl) :
    ∃ _ : IsIntegral (pullback π g), IsCov (π ≫ q) D (pullback.fst π g) := by
  have := hg.1.isLocallyNoetherian
  have := hq.isLocallyNoetherian
  have hfl' := FlagBaseChange.isFlagBundle_pullFlag B Y B₁ π g ι E r fl hfl
  have hE' (a) : IsVB ((Scheme.Modules.pullback g).obj (E a)) (r a) := (hE a).pullback g
  have hsm := GlobalTheory.T.flag_bundle_smooth_relative_dimension B₁ _ (pullback.snd π g) ι _ _ _ hE' hfl'
  have hsm₀ := GlobalTheory.T.flag_bundle_smooth_relative_dimension B Y π ι _ _ _ hE hfl
  have hs' := GlobalTheory.T.flag_bundle_projection_surjective B₁ _ (pullback.snd π g) ι _ _ _ hE' hfl'
  have hs := GlobalTheory.T.flag_bundle_projection_surjective B Y π ι _ _ _ hE hfl
  have := GlobalTheory.T.flag_bundle_total_space_irreducible B₁ _ (pullback.snd π g) ι _ _ _ hE' hfl'
  have := SmoothOfRelativeDimension.smooth (∑ a, r a * (r a - 1) / 2) (pullback.snd π g)
  have := GlobalTheory.geometricallyReduced_of_smooth (pullback.snd π g)
  have := GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian (pullback.snd π g)
  have hI : IsIntegral (pullback π g : Scheme.{0}) := isIntegral_of_irreducibleSpace_of_isReduced _
  have hπ : π (genericPoint Y) = genericPoint B := by
    obtain ⟨y, hy⟩ := hs (genericPoint B)
    exact LineBundleBaseChange.map_genericPoint_of_mem π y hy
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := π) (g := g) _ _ (hπ.trans hg.2.1.symm)
  refine ⟨hI, ⟨hq.isDomain, hq.finite, hI, isProjOver_pullback_fst hq hp.isProjOver hg.1.isProjOver, ?_, ?_⟩,
    LineBundleBaseChange.map_genericPoint_of_mem _ z hz₁, LineBundleBaseChange.residueDegree_fst_ne_zero π g _ ?_⟩
  · rw [← Category.assoc (pullback.fst π g), pullback.condition, Category.assoc (pullback.snd π g),
      Category.assoc (pullback.snd π g)]
    have := hg.1.flat
    infer_instance
  · rw [GlobalTheory.T.krull_dim_smooth_surjective_total B₁ _ (pullback.snd π g) (∑ a, r a * (r a - 1) / 2) d hs' hg.1.dim_eq,
      ← GlobalTheory.T.krull_dim_smooth_surjective_total B Y π (∑ a, r a * (r a - 1) / 2) d hs hq.dim_eq]
    exact hp.dim_eq
  · rw [LineBundleBaseChange.map_genericPoint_of_mem _ z hz₂]
    exact hg.2.2

end Covers

section Metrics

variable {k : Type} [CommRing k] {X Y₁ Y₂ Z : Scheme.{0}} {p : X ⟶ Sp k} {p₁ : Y₁ ⟶ Sp k} {p₂ : Y₂ ⟶ Sp k} {s : Z ⟶ Sp k}

theorem form_sum_left {σ : k →+* ℂ} {E : X.Modules} {r : ℕ} (m : Met p σ E r) {V : X.Opens} {ι : Type} [Fintype ι]
    (g : ι → Γ(X, V)) (e : ι → Γ(E, V)) (t : Γ(E, V)) (y : CxPts p σ) :
    m.form (∑ i, g i • e i) t y = ∑ i, CxPts.ev p σ V (g i) y * m.form (e i) t y :=
  (map_sum (AddMonoidHom.mk' (fun s : Γ(E, V) => m.form s t y) fun s s' => m.form_add_left s s' t y) _ _).trans
    (Finset.sum_congr rfl fun i _ => m.form_smul_left (g i) (e i) t y)

theorem form_eq_of_chart {σ : k →+* ℂ} {E E' : X.Modules} {r : ℕ} (m : Met p σ E r) (m' : Met p σ E' r) (u : E ⟶ E')
    (c : Chart E r) {y : CxPts p σ} (hc : y ∈ CxPts.ptsIn p σ c.U)
    (H : ∀ a b, m'.form (u.app _ (c.e a)) (u.app _ (c.e b)) y = m.form (c.e a) (c.e b) y) {V : X.Opens}
    (s t : Γ(E, V)) (hy : y ∈ CxPts.ptsIn p σ V) : m'.form (u.app V s) (u.app V t) y = m.form s t y := by
  have hW := CxPts.mem_ptsIn_inf.2 ⟨hy, hc⟩
  have step (s t : Γ(E, V ⊓ c.U)) (h : ∀ a, m'.form (u.app _ (Twist.resM E inf_le_right (c.e a))) (u.app _ t) y =
      m.form (Twist.resM E inf_le_right (c.e a)) t y) : m'.form (u.app _ s) (u.app _ t) y = m.form s t y := by
    rw [← (c.isFrame.basis inf_le_right).sum_repr s]
    simp only [map_sum, Scheme.Modules.Hom.app_smul, form_sum_left, IsFrame.basis_apply, h]
  rw [← m.form_resM s t inf_le_left hW, ← m'.form_resM _ _ inf_le_left hW, ← Twist.app_resM, ← Twist.app_resM]
  refine step _ _ fun a => ?_
  rw [← m.conj_form, ← m'.conj_form]
  refine congrArg _ (step _ _ fun b => ?_)
  rw [Twist.app_resM, Twist.app_resM, m.form_resM _ _ _ hW, m'.form_resM _ _ _ hW, H]

theorem isoHom_pull {E E' : X.Modules} {r : ℕ} {h : VMetric p E r} {h' : VMetric p E' r} {u : E ⟶ E'} (H : IsoHom h h' u)
    (π : Y₁ ⟶ X) (w : π ≫ p = p₁) : IsoHom (h.pull π w) (h'.pull π w) ((Scheme.Modules.pullback π).map u) := by
  intro σ V s s' z hz
  have hc := h.isVB.mem_pick (Points.PtsOver.map π w _ z)
  refine form_eq_of_chart ((h.met σ).pull π w) ((h'.met σ).pull π w) _ ((h.isVB.pick _).pull h.isVB π) hc
    (fun a b => ?_) s s' hz
  refine Eq.trans ?_ ((h.met σ).form_pull π w _ _ le_rfl hc).symm
  refine Eq.trans ?_ (((h'.met σ).form_pull π w _ _ le_rfl hc).trans (H σ _ _ _ _ hc))
  rw [← QCoh.pullback_map_app_pullbackSections, ← QCoh.pullback_map_app_pullbackSections]
  rfl

variable {f₁ : Y₁ ⟶ X} {f₂ : Y₂ ⟶ X} {t₁ : Z ⟶ Y₁} {t₂ : Z ⟶ Y₂}

def sqIso (e : t₁ ≫ f₁ = t₂ ≫ f₂) : Scheme.Modules.pullback f₁ ⋙ Scheme.Modules.pullback t₁ ≅
    Scheme.Modules.pullback f₂ ⋙ Scheme.Modules.pullback t₂ :=
  Scheme.Modules.pullbackComp t₁ f₁ ≪≫ Scheme.Modules.pullbackCongr e ≪≫ (Scheme.Modules.pullbackComp t₂ f₂).symm

theorem isIsometry_sqIso (e : t₁ ≫ f₁ = t₂ ≫ f₂) {E : X.Modules} {r : ℕ} (h : VMetric p E r) (w₁ : f₁ ≫ p = p₁)
    (w₂ : f₂ ≫ p = p₂) (v₁ : t₁ ≫ p₁ = s) (v₂ : t₂ ≫ p₂ = s) :
    ((h.pull f₁ w₁).pull t₁ v₁).IsIsometry ((h.pull f₂ w₂).pull t₂ v₂) ((sqIso e).app E) := by
  obtain ⟨-, hc⟩ := VMetric.isIsometry_pull_id_comp k X p E r h
  have e₁ : (t₁ ≫ f₁) ≫ p = s := by rw [Category.assoc, w₁, v₁]
  have e₂ : (t₂ ≫ f₂) ≫ p = s := by rw [Category.assoc, w₂, v₂]
  have I := IsometryPullback.isIsometry_trans (hc Y₁ _ p₁ _ f₁ t₁ w₁ v₁ e₁)
    (IsometryPullback.isIsometry_trans (Reduce.isIsometry_pullbackCongr h e e₁ e₂)
      (IsometryPullback.isIsometry_symm (hc Y₂ _ p₂ _ f₂ t₂ w₂ v₂ e₂)))
  have e₃ : (sqIso e).app E = (Scheme.Modules.pullbackComp t₁ f₁).app E ≪≫ (Scheme.Modules.pullbackCongr e).app E ≪≫
      ((Scheme.Modules.pullbackComp t₂ f₂).app E).symm := Iso.ext rfl
  rw [e₃]
  exact I

theorem isometric_sq (e : t₁ ≫ f₁ = t₂ ≫ f₂) (A : HermLB p) (w₁ : f₁ ≫ p = p₁)
    (w₂ : f₂ ≫ p = p₂) (v₁ : t₁ ≫ p₁ = s) (v₂ : t₂ ≫ p₂ = s) :
    ((A.pull f₁ w₁).pull t₁ v₁).Isometric ((A.pull f₂ w₂).pull t₂ v₂) := by
  have e₁ : (t₁ ≫ f₁) ≫ p = s := by rw [Category.assoc, w₁, v₁]
  have e₂ : (t₂ ≫ f₂) ≫ p = s := by rw [Category.assoc, w₂, v₂]
  exact (HermLB.isometric_of_refines (HermLB.refines_pull_pull A f₁ w₁ t₁ v₁ e₁)).trans
    ((HermLB.isometric_pull_of_eq A e e₁ e₂).trans
      (HermLB.isometric_of_refines (HermLB.refines_pull_comp A f₂ w₂ t₂ v₂ e₂)))

theorem isometric_grLB_pull_ofIso {E : X.Modules} {F : Y₁.Modules} {r : ℕ} {h : VMetric p E r} {h' : VMetric p₁ F r}
    (H : h.IsCInf) (H' : h'.IsCInf) (w : f₁ ≫ p = p₁) {φ : (Scheme.Modules.pullback f₁).obj E ≅ F}
    (I : (h.pull f₁ w).IsIsometry h' φ) (fl : Vert.Flag E r) (i : Fin r) :
    ((VMetric.grLB fl i H).pull f₁ w).Isometric (VMetric.grLB ((fl.pull f₁).ofIso φ) i H') := by
  rw [VMetric.grLB_ofIso I (H.pull f₁ w)]
  exact (VMetric.isometric_grLB_pull k X _ p _ _ r h H fl f₁ w i).symm

end Metrics

theorem vanish_of_cov (hA : Published.ArCalc) {k : Type} [CommRing k] {X Z : Scheme.{0}} [IsIntegral X] [IsIntegral Z]
    {p : X ⟶ Sp k} {t : Z ⟶ X} {n e : ℕ} (hp : IsArithVar p (n + 1 + e)) (ht : IsCov p (n + 1 + e) t) {ι : Type}
    [Fintype ι] {r : ι → ℕ} {x x' : (Σ a, Fin (r a)) → HermLB p} {y y' : (Σ a, Fin (r a)) → HermLB (t ≫ p)}
    (I : ∀ z, ((x z).pull t rfl).Isometric (y z)) (I' : ∀ z, ((x' z).pull t rfl).Isometric (y' z))
    (H : Vanish n e y y') : Vanish n e x x' := by
  intro Φ hΦ Q hQ hQ'
  have h₁ := (hA.arProj k X Z p _ _ hp ht.1 t rfl ht.2.1 ht.2.2).2 _ _ Φ hΦ
  have h₂ := ((hA.arIso k Z _ _ ht.1).2 _ _ _ h₁).2.1 (Sum.elim y y') (by rintro (z | z); exacts [I z, I' z])
  have h₃ := H _ h₂ Q hQ hQ'
  rw [LinearMap.smul_apply, smul_eq_mul] at h₃
  exact (mul_eq_zero.1 h₃).resolve_left (Nat.cast_ne_zero.2 ht.2.2)

theorem vanishOn_of_regFlagged : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.RegularAlteration → VanishOn RegFlagged →
    VanishOn fun _ _ _ _ _ _ => True := by
  intro hP hR hV k _ B Y X _ _ _ q π ρ p w n e hq hπ hρ ι _ E E' r h h' H H' u hu _ fl hfl fl' hc
  subst w
  obtain ⟨B₁, g, _, hg, hreg⟩ := exists_cov_regFlagged hR hq u (fun a => (h a).isVB) fun a => (h' a).isVB
  obtain ⟨_, hf⟩ := isCov_pullback_fst hq hπ hg (fun a => (h a).isVB) hfl
  obtain ⟨Z, _, t₁, t₂, et, h₁, h₂⟩ := exists_common_cov hπ hρ hf
  have w₁ : pullback.fst π g ≫ π ≫ q = pullback.snd π g ≫ g ≫ q := pullback.condition_assoc q
  have w₂ : t₂ ≫ pullback.snd π g ≫ g ≫ q = t₁ ≫ ρ ≫ π ≫ q := by rw [← w₁, reassoc_of% et]
  let ε : Scheme.Modules.pullback π ⋙ Scheme.Modules.pullback ρ ⋙ Scheme.Modules.pullback t₁ ≅
      (Scheme.Modules.pullback g ⋙ Scheme.Modules.pullback (pullback.snd π g)) ⋙ Scheme.Modules.pullback t₂ :=
    Functor.isoWhiskerLeft _ (sqIso et) ≪≫
      Functor.isoWhiskerRight (sqIso pullback.condition) (Scheme.Modules.pullback t₂)
  have key := hV k B₁ (pullback π g) Z (g ≫ q) (pullback.snd π g) t₂ _ w₂ n e hg.1 (w₁ ▸ hf.1) (w₁ ▸ h₂) ι _ _ r
    (fun a => (h a).pull g rfl) (fun a => (h' a).pull g rfl) (fun a => (H a).pull g rfl) (fun a => (H' a).pull g rfl)
    _ (fun a => isoHom_pull (hu a) g rfl) hreg _ (FlagBaseChange.isFlagBundle_pullFlag B Y B₁ π g ι E r fl hfl)
    (fun a => ((fl' a).pull t₁).ofIso (ε.app (E' a))) fun a => by
      refine compat_of_le (compat_ofIso ((hc a).pull t₁) (ε.app (E a)) (ε.app (E' a)) (ε.hom.naturality (u a)).symm)
        fun i => ?_
      refine ⟨(sqIso et).inv.app ((fl a).F i), ?_⟩
      change _ ≫ (Scheme.Modules.pullback ρ ⋙ Scheme.Modules.pullback t₁).map ((fl a).ι i) ≫ (sqIso et).hom.app _ ≫
          (Scheme.Modules.pullback t₂).map ((sqIso pullback.condition).hom.app (E a)) =
        (Scheme.Modules.pullback t₂).map ((Scheme.Modules.pullback (pullback.fst π g)).map ((fl a).ι i) ≫
          (sqIso pullback.condition).hom.app (E a))
      rw [NatTrans.naturality_assoc, Iso.inv_hom_id_app_assoc, Functor.map_comp]
      rfl
  refine vanish_of_cov hP.p4 hρ.1 h₁ (fun z => ?_) (fun z => ?_) key
  · exact (isometric_sq et _ rfl w₁ rfl w₂).trans ((isometric_grLB_pull_ofIso _ _ w₁
      (isIsometry_sqIso pullback.condition (h z.1) rfl rfl w₁ rfl) (fl z.1) z.2).pull t₂ w₂)
  · exact isometric_grLB_pull_ofIso _ _ rfl (IsometryPullback.isIsometry_trans
      (isIsometry_sqIso et ((h' z.1).pull π rfl) rfl w₁ rfl w₂)
      (IsometryPullback.isIsometry_pull (isIsometry_sqIso pullback.condition (h' z.1) rfl rfl w₁ rfl) t₂ w₂)) (fl' z.1) z.2

end GlobalTheory.TwoLat.Gen

end
