import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FinCover
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.BlowUpOff

noncomputable section

open CategoryTheory Limits AlgebraicGeometry UpperTheory.Gal.DifferentialFormSections
open FunctorialResolution.Blowup
open GroundTheory.Arith.SchemeCoh (inter inter_le inter_le_comp mem_inter_iff)

namespace UpperTheory.Gal.KunnethLefschetz.G

section
variable {Y : Scheme.{0}}

private abbrev rs {U V : Y.Opens} (h : V ≤ U) : Γ(Y, U) →+* Γ(Y, V) := (Y.presheaf.map (homOfLE h).op).hom

private theorem rs_rs {U V T : Y.Opens} (h : V ≤ U) (h' : T ≤ V) (x : Γ(Y, U)) :
    rs h' (rs h x) = rs (h'.trans h) x := by
  change ((Y.presheaf.map (homOfLE h).op ≫ Y.presheaf.map (homOfLE h').op)).hom x = _
  rw [← Functor.map_comp]
  rfl

private theorem nzd_rs {U V : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (h : V ≤ U)
    {s : Γ(Y, U)} (hs : s ∈ nonZeroDivisors Γ(Y, U)) : rs h s ∈ nonZeroDivisors Γ(Y, V) := by
  have hf : (Scheme.Hom.appLE (𝟙 Y) U V h).hom.Flat :=
    HasRingHomProperty.appLE (P := @Flat) (Q := RingHom.Flat) (𝟙 Y) inferInstance ⟨U, hU⟩ ⟨V, hV⟩ h
  have e : (Scheme.Hom.appLE (𝟙 Y) U V h).hom = rs h := by
    ext x
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]
    rfl
  rw [e] at hf
  letI : Algebra Γ(Y, U) Γ(Y, V) := (rs h).toAlgebra
  haveI : Module.Flat Γ(Y, U) Γ(Y, V) := hf
  have hr : IsSMulRegular Γ(Y, U) s := fun a b e => (mul_cancel_left_mem_nonZeroDivisors hs).1 e
  have hr' := IsSMulRegular.of_flat (S := Γ(Y, V)) hr
  rw [mem_nonZeroDivisors_iff_right]
  intro x hx
  apply hr'
  change rs h s * x = rs h s * 0
  rw [mul_zero, mul_comm]
  exact hx

private theorem exists_unit (J : Y.IdealSheafData) {U₁ U₂ T : Y.Opens}
    (a₁ : IsAffineOpen U₁) (a₂ : IsAffineOpen U₂) (aT : IsAffineOpen T) (h₁ : T ≤ U₁) (h₂ : T ≤ U₂)
    {s₁ : Γ(Y, U₁)} {s₂ : Γ(Y, U₂)} (e₁ : J.ideal ⟨U₁, a₁⟩ = Ideal.span {s₁})
    (e₂ : J.ideal ⟨U₂, a₂⟩ = Ideal.span {s₂})
    (n₂ : s₂ ∈ nonZeroDivisors Γ(Y, U₂)) :
    ∃ g : Γ(Y, T)ˣ, rs h₁ s₁ = g.val * rs h₂ s₂ := by
  have key : ∀ {U : Y.Opens} (a : IsAffineOpen U) (h : T ≤ U) {s : Γ(Y, U)},
      J.ideal ⟨U, a⟩ = Ideal.span {s} → J.ideal ⟨T, aT⟩ = Ideal.span {rs h s} := by
    intro U a h s e
    have := J.map_ideal (U := ⟨T, aT⟩) (V := ⟨U, a⟩) h
    rw [e, Ideal.map_span, Set.image_singleton] at this
    exact this.symm
  have k₁ := key a₁ h₁ e₁
  have k₂ := key a₂ h₂ e₂
  have m₁ : rs h₁ s₁ ∈ Ideal.span {rs h₂ s₂} := by
    rw [← k₂, k₁]; exact Ideal.mem_span_singleton_self _
  have m₂ : rs h₂ s₂ ∈ Ideal.span {rs h₁ s₁} := by
    rw [← k₁, k₂]; exact Ideal.mem_span_singleton_self _
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 m₁
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 m₂
  have n := nzd_rs a₂ aT h₂ n₂
  have hab : a * b = 1 := by
    refine (mul_cancel_left_mem_nonZeroDivisors n).1 ?_
    calc rs h₂ s₂ * (a * b) = b * (a * rs h₂ s₂) := by ring
      _ = rs h₂ s₂ * 1 := by rw [ha, hb, mul_one]
  exact ⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, ha.symm⟩

end

section
variable {K : Type} [CommRing K] {X : Sch K}

private theorem secRes_eq {U V : X.left.Opens} (h : V ≤ U) (x : Sec X U) :
    secRes X h x = rs h x := by
  change (Scheme.Hom.appLE (𝟙 X.left) U V h).hom x = _
  simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]
  rfl

private abbrev Idx (J : X.left.IdealSheafData) : Type :=
  Σ V : X.left.affineOpens, {s : Γ(X.left, V.1) // J.ideal V = Ideal.span {s} ∧ s ∈ nonZeroDivisors Γ(X.left, V.1)}

private abbrev idxU (J : X.left.IdealSheafData) (j : Idx J) : X.left.Opens := j.1.1

private theorem aff2 [X.left.IsSeparated] (J : X.left.IdealSheafData) (i : Fin 2 → Idx J) :
    IsAffineOpen (cap (X := X) (idxU J) i) := by
  have : cap (X := X) (idxU J) i = idxU J (i 0) ⊓ idxU J (i 1) := by
    ext x
    simp [mem_inter_iff, Fin.forall_fin_two]
  rw [this]
  exact (i 0).1.2.inf (i 1).1.2

private theorem aff3 [X.left.IsSeparated] (J : X.left.IdealSheafData) (i : Fin 3 → Idx J) :
    IsAffineOpen (cap (X := X) (idxU J) i) := by
  have : cap (X := X) (idxU J) i = idxU J (i 0) ⊓ idxU J (i 1) ⊓ idxU J (i 2) := by
    ext x
    simp [mem_inter_iff, Fin.forall_fin_succ, and_assoc]
  rw [this]
  exact ((i 0).1.2.inf (i 1).1.2).inf (i 2).1.2

private theorem exists_g [X.left.IsSeparated] (J : X.left.IdealSheafData) (i : Fin 2 → Idx J) :
    ∃ g : Γ(X.left, cap (X := X) (idxU J) i)ˣ, rs (inter_le (X := X.left.toTopCat) (idxU J) i 0) (i 0).2.1 =
      g.val * rs (inter_le (X := X.left.toTopCat) (idxU J) i 1) (i 1).2.1 :=
  exists_unit J (i 0).1.2 (i 1).1.2 (aff2 J i) _ _ (i 0).2.2.1 (i 1).2.2.1 (i 1).2.2.2

private def gg [X.left.IsSeparated] (J : X.left.IdealSheafData) (i : Fin 2 → Idx J) : Γ(X.left, cap (X := X) (idxU J) i)ˣ :=
  (exists_g (X := X) J i).choose

private theorem gg_spec [X.left.IsSeparated] (J : X.left.IdealSheafData) {T : X.left.Opens} (j : Fin 2 → Idx J)
    (a c : Idx J) (ha : j 0 = a) (hc : j 1 = c) (hT : T ≤ cap (X := X) (idxU J) j) (ta : T ≤ idxU J a) (tc : T ≤ idxU J c) :
    rs ta a.2.1 = rs hT (gg (X := X) J j).val * rs tc c.2.1 := by
  subst ha hc
  have e := congrArg (rs hT) (exists_g (X := X) J j).choose_spec
  rw [map_mul, rs_rs, rs_rs] at e
  exact e

private theorem gg_coc [X.left.IsSeparated] (J : X.left.IdealSheafData) (i : Fin 3 → Idx J) :
    rs (inter_le_comp (X := X.left.toTopCat) (idxU J) i (Fin.succAbove 2)) (gg (X := X) J (i ∘ Fin.succAbove 2)).val *
      rs (inter_le_comp (X := X.left.toTopCat) (idxU J) i (Fin.succAbove 0)) (gg (X := X) J (i ∘ Fin.succAbove 0)).val =
      rs (inter_le_comp (X := X.left.toTopCat) (idxU J) i (Fin.succAbove 1)) (gg (X := X) J (i ∘ Fin.succAbove 1)).val := by
  have t : ∀ a, cap (X := X) (idxU J) i ≤ idxU J (i a) := inter_le (X := X.left.toTopCat) (idxU J) i
  have A := gg_spec (X := X) J (i ∘ Fin.succAbove 2) (i 0) (i 1) rfl rfl
    (inter_le_comp (X := X.left.toTopCat) (idxU J) i (Fin.succAbove 2)) (t 0) (t 1)
  have B := gg_spec (X := X) J (i ∘ Fin.succAbove 0) (i 1) (i 2) rfl rfl
    (inter_le_comp (X := X.left.toTopCat) (idxU J) i (Fin.succAbove 0)) (t 1) (t 2)
  have C := gg_spec (X := X) J (i ∘ Fin.succAbove 1) (i 0) (i 2) rfl rfl
    (inter_le_comp (X := X.left.toTopCat) (idxU J) i (Fin.succAbove 1)) (t 0) (t 2)
  refine (mul_cancel_right_mem_nonZeroDivisors (nzd_rs (i 2).1.2 (aff3 J i) (t 2) (i 2).2.2.2)).1 ?_
  rw [← C, mul_assoc, ← B, ← A]

private theorem exists_coc [X.left.IsSeparated] (J : X.left.IdealSheafData) (hJ : IsLocallyGeneratedByNonZeroDivisor J) :
    ∃ (L : Coc X) (s : ∀ j : L.ι, Sec X (L.U j)) (a : ∀ j, IsAffineOpen (L.U j)),
      (∀ j, J.ideal ⟨L.U j, a j⟩ = Ideal.span {(s j : Γ(X.left, L.U j))}) ∧
      (∀ j, s j ∈ nonZeroDivisors (Sec X (L.U j))) ∧
      ∀ j : Fin 2 → L.ι, secRes X (inter_le (X := X.left.toTopCat) L.U j 0) (s (j 0)) =
        (L.g j).val * secRes X (inter_le (X := X.left.toTopCat) L.U j 1) (s (j 1)) := by
  refine ⟨{ ι := Idx J, U := idxU J, cov := ⟨fun j => j.1.2, ?_⟩, g := gg (X := X) J, coc := ?_ }, fun j => j.2.1,
    fun j => j.1.2, fun j => j.2.2.1, fun j => j.2.2.2, fun j => ?_⟩
  · refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨U, f, hx, hf, e⟩ := hJ x
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨U, f, e, hf⟩, hx⟩
  · intro i
    simp only [secRes_eq]
    exact gg_coc (X := X) J i
  · refine (secRes_eq _ _).trans (((exists_g (X := X) J j).choose_spec).trans ?_)
    exact congrArg (fun t => (gg (X := X) J j).val * t) (secRes_eq _ _).symm

end

theorem exDiv : ExDiv := by
  intro R _ _ Z W D _ _ π hπ
  haveI : Smooth Z.hom := SmoothOfRelativeDimension.smooth D Z.hom
  obtain ⟨hp, hcl, -⟩ := blOff R π hπ
  haveI : IsProper π.left := hp
  haveI : IsClosedImmersion (dg Z).left := by
    change IsClosedImmersion (pullback.diagonal Z.hom)
    infer_instance
  haveI : IsSeparated (XX Z).hom := by
    change IsSeparated (pullback.fst Z.hom Z.hom ≫ Z.hom)
    infer_instance
  haveI : IsSeparated W.hom := by
    rw [← Over.w π]
    infer_instance
  haveI : W.left.IsSeparated := by
    constructor
    have : terminal.from W.left = W.hom ≫ terminal.from _ := terminal.hom_ext _ _
    rw [this]
    infer_instance
  obtain ⟨L, s, a, h1, h2, h3⟩ := exists_coc (X := W) _ hπ.1
  haveI : IsClosedImmersion (exI π).left := hcl
  refine ⟨L, s, hcl, fun j => ?_, h2, h3⟩
  have e : (exI π).left.ker = (dg Z).left.ker.comap π.left :=
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion (dg Z).left π.left
  have e2 := Scheme.Hom.ker_apply (exI π).left ⟨L.U j, a j⟩
  rw [e, h1 j] at e2
  refine Eq.trans ?_ e2.symm
  change RingHom.ker (Scheme.Hom.appLE (exI π).left (L.U j) _ le_rfl).hom = _
  rw [Scheme.Hom.appLE_eq_app]

end UpperTheory.Gal.KunnethLefschetz.G
