import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory groupCohomology Rep

universe u

variable (k G : Type u) [CommRing k] [Group G] (X : Type u) [AddCommGroup X] [Module k X]

noncomputable def coindOneRep : Representation k G (G → X) where
  toFun g := LinearMap.funLeft k X (· * g)
  map_one' := by ext; simp
  map_mul' g h := by ext; simp [mul_assoc]

@[simp]
lemma coindOneRep_apply (g : G) (F : G → X) (x : G) : coindOneRep k G X g F x = F (x * g) := rfl

noncomputable abbrev coindOne : Rep k G := Rep.of (coindOneRep k G X)

instance : Subsingleton (⊥ : Subgroup G) :=
  ⟨fun a b => Subtype.ext <| by rw [Subgroup.mem_bot.1 a.2, Subgroup.mem_bot.1 b.2]⟩

noncomputable def coindOneIsoCoind :
    coindOne k G X ≅ coind (⊥ : Subgroup G).subtype (Rep.trivial k (⊥ : Subgroup G) X) :=
  Rep.mkIso <| Representation.Equiv.mk
    { toFun := fun F => ⟨F, fun g h => by rw [Subsingleton.elim g 1]; simp⟩
      invFun := Subtype.val
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    (fun _ => LinearMap.ext fun _ => Subtype.ext rfl)

theorem isZero_coindOne (n : ℕ) : Limits.IsZero (groupCohomology (coindOne k G X) (n + 1)) :=
  (isZero_groupCohomology_succ_of_subsingleton (Rep.trivial k (⊥ : Subgroup G) X) n).of_iso
    ((groupCohomology.functor k G (n + 1)).mapIso (coindOneIsoCoind k G X) ≪≫
      groupCohomology.coindIso _ (n + 1))

variable {G} (S : Subgroup G)

lemma out_inv_mul_mem (x : G) : ((x : G ⧸ S).out)⁻¹ * x ∈ S :=
  QuotientGroup.leftRel_apply.1 (Quotient.exact' (QuotientGroup.out_eq' (x : G ⧸ S)))

noncomputable def cosetPart (x : G) : S := ⟨((x : G ⧸ S).out)⁻¹ * x, out_inv_mul_mem S x⟩

lemma out_mul_cosetPart (x : G) : (x : G ⧸ S).out * (cosetPart S x : G) = x := by
  simp [cosetPart]

lemma mk_out_mul (c : G ⧸ S) (s : S) : ((c.out * s : G) : G ⧸ S) = c := by
  conv_rhs => rw [← QuotientGroup.out_eq' c]
  exact (QuotientGroup.eq).2 (by simp)

lemma cosetPart_out_mul (c : G ⧸ S) (s : S) : cosetPart S (c.out * s) = s := by
  apply Subtype.ext
  simp [cosetPart]

noncomputable def resCoindOneIso :
    res S.subtype (coindOne k G X) ≅ coindOne k S (G ⧸ S → X) :=
  Rep.mkIso <| Representation.Equiv.mk
    { toFun := fun F s c => F (c.out * s)
      invFun := fun F x => F (cosetPart S x) x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun F => funext fun x => by
        simp only
        rw [out_mul_cosetPart]
      right_inv := fun F => funext fun s => funext fun c => by
        simp only
        rw [cosetPart_out_mul, mk_out_mul] }
    (fun t => LinearMap.ext fun F => funext fun s => funext fun c => by
      simp [mul_assoc])

noncomputable def quotientToInvariantsCoindOneIso [S.Normal] :
    (coindOne k G X).quotientToInvariants S ≅ coindOne k (G ⧸ S) X :=
  Rep.mkIso <| Representation.Equiv.mk
    { toFun := fun F c => Quotient.liftOn' c F.1 fun x y hxy => by
        have h := congrFun (F.2 ⟨x⁻¹ * y, QuotientGroup.leftRel_apply.1 hxy⟩) x
        simpa using h.symm
      invFun := fun F => ⟨fun x => F x, fun s => funext fun x => by
        simp⟩
      map_add' := fun F F' => funext fun c => by
        induction c using QuotientGroup.induction_on; rfl
      map_smul' := fun r F => funext fun c => by
        induction c using QuotientGroup.induction_on; rfl
      left_inv := fun F => Subtype.ext rfl
      right_inv := fun F => funext fun c => by
        induction c using QuotientGroup.induction_on; rfl }
    (fun g => by
      induction g using QuotientGroup.induction_on
      exact LinearMap.ext fun F => funext fun c => by
        induction c using QuotientGroup.induction_on; rfl)

theorem isZero_res_coindOne (n : ℕ) :
    Limits.IsZero (groupCohomology (res S.subtype (coindOne k G X)) (n + 1)) :=
  (isZero_coindOne k S (G ⧸ S → X) n).of_iso
    ((groupCohomology.functor k S (n + 1)).mapIso (resCoindOneIso k X S))

theorem isZero_quotientToInvariants_coindOne [S.Normal] (n : ℕ) :
    Limits.IsZero (groupCohomology ((coindOne k G X).quotientToInvariants S) (n + 1)) :=
  (isZero_coindOne k (G ⧸ S) X n).of_iso
    ((groupCohomology.functor k (G ⧸ S) (n + 1)).mapIso (quotientToInvariantsCoindOneIso k X S))

end GroundTheory.GroupCoh
