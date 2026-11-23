import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TupleActions.InstMulActionTup

open CategoryTheory

private theorem term_congr {G : Type} [Group G] (S : Subgroup G) (A : Rep.{0} ℂ G)
    (F : Representation.coindV S.subtype (Rep.res S.subtype A).ρ) {g g' : G}
    (h : (g : G ⧸ S) = (g' : G ⧸ S)) : A.ρ g (F.1 g⁻¹) = A.ρ g' (F.1 g'⁻¹) := by
  have hs : g⁻¹ * g' ∈ S := QuotientGroup.eq.mp h
  let s : S := ⟨g⁻¹ * g', hs⟩
  have hF : F.1 (S.subtype s⁻¹ * g⁻¹) = (Rep.res S.subtype A).ρ s⁻¹ (F.1 g⁻¹) := F.2 s⁻¹ g⁻¹
  have hg : S.subtype s⁻¹ * g⁻¹ = g'⁻¹ := by
    show (g⁻¹ * g')⁻¹ * g⁻¹ = g'⁻¹
    group
  rw [hg] at hF
  rw [hF]
  show _ = A.ρ g' (A.ρ (g⁻¹ * g')⁻¹ (F.1 g⁻¹))
  rw [← Module.End.mul_apply, ← map_mul, show g' * (g⁻¹ * g')⁻¹ = g by group]

private noncomputable def tr {G : Type} [Group G] (S : Subgroup G) [Fintype (G ⧸ S)] (A : Rep.{0} ℂ G) :
    Representation.coindV S.subtype (Rep.res S.subtype A).ρ →ₗ[ℂ] A :=
  ∑ q : G ⧸ S, A.ρ q.out ∘ₗ LinearMap.proj q.out⁻¹ ∘ₗ Submodule.subtype _

private theorem tr_apply {G : Type} [Group G] (S : Subgroup G) [Fintype (G ⧸ S)] (A : Rep.{0} ℂ G)
    (F : Representation.coindV S.subtype (Rep.res S.subtype A).ρ) :
    tr S A F = ∑ q : G ⧸ S, A.ρ q.out (F.1 q.out⁻¹) := by
  rw [tr, LinearMap.sum_apply]
  rfl

private theorem tr_equiv {G : Type} [Group G] (S : Subgroup G) [Fintype (G ⧸ S)] (A : Rep.{0} ℂ G) (h : G)
    (F : Representation.coindV S.subtype (Rep.res S.subtype A).ρ) :
    tr S A (Representation.coind S.subtype (Rep.res S.subtype A).ρ h F) = A.ρ h (tr S A F) := by
  rw [tr_apply, tr_apply, map_sum]
  refine Fintype.sum_equiv (MulAction.toPerm h⁻¹ : Equiv.Perm (G ⧸ S)) _ _ ?_
  intro q
  have hq : ((h⁻¹ * q.out : G) : G ⧸ S) = (((MulAction.toPerm h⁻¹ : Equiv.Perm (G ⧸ S)) q).out : G) := by
    rw [QuotientGroup.out_eq']
    show _ = h⁻¹ • q
    rw [← QuotientGroup.out_eq' q, MulAction.Quotient.smul_mk, QuotientGroup.out_eq']
    rfl
  rw [← term_congr S A F hq]
  show A.ρ q.out (F.1 (q.out⁻¹ * h)) = _
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left, mul_inv_rev, inv_inv]

theorem UpperTheory.coind_retract_of_finite_index :
    UpperTheory.V.Af.BA.CoindRetract := by
  classical
  unfold UpperTheory.V.Af.BA.CoindRetract
  intro G _ S hS A
  haveI := hS
  haveI : Fintype (G ⧸ S) := Fintype.ofFinite _
  have hn : (Fintype.card (G ⧸ S) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  let P : A →ₗ[ℂ] Representation.coindV S.subtype (Rep.res S.subtype A).ρ :=
    { toFun := fun a => ⟨fun g => A.ρ g a, fun s g => by
        show A.ρ (S.subtype s * g) a = A.ρ (S.subtype s) (A.ρ g a)
        rw [map_mul, Module.End.mul_apply]⟩
      map_add' := fun a b => Subtype.ext (funext fun g => map_add (A.ρ g) a b)
      map_smul' := fun c a => Subtype.ext (funext fun g => map_smul (A.ρ g) c a) }
  let π : A ⟶ Rep.coind S.subtype (Rep.res S.subtype A) :=
    Rep.ofHom ⟨P, fun h => LinearMap.ext fun a => Subtype.ext (funext fun g => by
      show A.ρ g (A.ρ h a) = A.ρ (g * h) a
      rw [map_mul, Module.End.mul_apply])⟩
  let ι : Rep.coind S.subtype (Rep.res S.subtype A) ⟶ A :=
    Rep.ofHom ⟨(Fintype.card (G ⧸ S) : ℂ)⁻¹ • tr S A, fun h => LinearMap.ext fun F => by
      simp only [LinearMap.comp_apply, LinearMap.smul_apply, map_smul]
      exact congrArg (fun x => (Fintype.card (G ⧸ S) : ℂ)⁻¹ • x) (tr_equiv S A h F)⟩
  refine ⟨π, ι, ?_⟩
  apply Rep.hom_ext
  ext a
  show (Fintype.card (G ⧸ S) : ℂ)⁻¹ • tr S A (P a) = a
  rw [tr_apply]
  have hterm : ∀ q : G ⧸ S, A.ρ q.out ((P a).1 q.out⁻¹) = a := fun q => by
    show A.ρ q.out (A.ρ q.out⁻¹ a) = a
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  rw [Finset.sum_congr rfl fun q _ => hterm q, Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hn, one_smul]
