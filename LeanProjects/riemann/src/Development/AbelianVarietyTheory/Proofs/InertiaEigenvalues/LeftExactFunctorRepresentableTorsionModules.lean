import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.H1MapSubgroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGeneratorsOfCardHomResidueFieldLeStatement
open CategoryTheory GlobalTheory.SelFun

namespace GlobalTheory.SelFun.Level

variable {Λ : Type} [CommRing Λ] [IsLocalRing Λ]

def IsMin (F : ModuleCat.{0} Λ ⥤ ModuleCat.{0} Λ) (A : ModuleCat.{0} Λ) (x : F.obj A) : Prop :=
  ∀ B : ModuleCat.{0} Λ, Tors Λ B → ∀ φ : A ⟶ B, (F.map φ).hom x = 0 → φ = 0

def LeftEx (F : ModuleCat.{0} Λ ⥤ ModuleCat.{0} Λ) : Prop :=
  ∀ (B' B B'' : ModuleCat.{0} Λ), Tors Λ B → Tors Λ B'' → ∀ (f : B' ⟶ B) (g : B ⟶ B''), Function.Injective f.hom →
      Function.Exact f.hom g.hom → Function.Injective (F.map f).hom ∧ Function.Exact (F.map f).hom (F.map g).hom

theorem map_map (F : ModuleCat.{0} Λ ⥤ ModuleCat.{0} Λ) {A B C : ModuleCat.{0} Λ} (f : A ⟶ B) (g : B ⟶ C)
    (x : F.obj A) : (F.map g).hom ((F.map f).hom x) = (F.map (f ≫ g)).hom x := by
  rw [F.map_comp]; rfl

theorem exists_min (F : ModuleCat.{0} Λ ⥤ ModuleCat.{0} Λ) (hF : LeftEx F) (A : ModuleCat.{0} Λ) [Finite A]
    (hA : Tors Λ A) (x : F.obj A) :
    ∃ (C : ModuleCat.{0} Λ) (f : C ⟶ A) (z : F.obj C), Function.Injective f.hom ∧ (F.map f).hom z = x ∧
      IsMin F C z := by
  classical
  have hex : ∃ m : ℕ, ∃ (C : ModuleCat.{0} Λ) (f : C ⟶ A) (z : F.obj C), Function.Injective f.hom ∧
      (F.map f).hom z = x ∧ Nat.card C = m :=
    ⟨_, A, 𝟙 A, x, Function.injective_id, by rw [F.map_id]; rfl, rfl⟩
  obtain ⟨C, f, z, hf, hz, hm⟩ := Nat.find_spec hex
  refine ⟨C, f, z, hf, hz, fun B hB φ hφ => ?_⟩
  haveI : Finite C := Finite.of_injective _ hf
  have hC : Tors Λ C := fun c => by
    obtain ⟨n, hn⟩ := hA (f.hom c)
    exact ⟨n, fun r hr => hf (by rw [map_smul, hn r hr, map_zero])⟩
  obtain ⟨-, h2⟩ := hF (ModuleCat.of Λ (LinearMap.ker φ.hom)) C B hC hB
    (ModuleCat.ofHom (LinearMap.ker φ.hom).subtype) φ Subtype.val_injective
    (LinearMap.exact_subtype_ker_map φ.hom)
  obtain ⟨w, hw⟩ := (h2 z).1 hφ
  have hle : Nat.find hex ≤ Nat.card (LinearMap.ker φ.hom) :=
    Nat.find_min' hex ⟨ModuleCat.of Λ (LinearMap.ker φ.hom),
      ModuleCat.ofHom (LinearMap.ker φ.hom).subtype ≫ f, w, hf.comp Subtype.val_injective,
      by rw [← map_map, hw, hz], rfl⟩
  rw [← hm] at hle
  have hbij : Function.Bijective (LinearMap.ker φ.hom).subtype :=
    Function.Injective.bijective_of_nat_card_le Subtype.val_injective hle
  ext c
  obtain ⟨k, rfl⟩ := hbij.2 c
  exact k.2

theorem card_le_of_min [IsNoetherianRing Λ] [Finite (IsLocalRing.ResidueField Λ)]
    (F : ModuleCat.{0} Λ ⥤ ModuleCat.{0} Λ) [F.Additive]
    (hfin : Finite (F.obj (ModuleCat.of Λ (IsLocalRing.ResidueField Λ)))) (n : ℕ) :
    ∃ N : ℕ, ∀ (A : ModuleCat.{0} Λ) (x : F.obj A), Finite A →
      (∀ r ∈ IsLocalRing.maximalIdeal Λ ^ n, ∀ y : A, r • y = 0) → IsMin F A x → Nat.card A ≤ N := by
  set c := Nat.card (F.obj (ModuleCat.of Λ (IsLocalRing.ResidueField Λ))) with hc
  haveI : Finite (Λ ⧸ IsLocalRing.maximalIdeal Λ) := ‹Finite (IsLocalRing.ResidueField Λ)›
  haveI : Finite (Λ ⧸ IsLocalRing.maximalIdeal Λ ^ n) :=
    Ideal.finite_quotient_pow (IsNoetherian.noetherian _) n
  refine ⟨Nat.card (Fin c → Λ ⧸ IsLocalRing.maximalIdeal Λ ^ n), fun A x hA hn hmin => ?_⟩
  have hk : Tors Λ (IsLocalRing.ResidueField Λ) := fun b => ⟨1, fun r hr => by
    rw [pow_one] at hr
    rw [Algebra.smul_def, IsLocalRing.ResidueField.algebraMap_eq,
      (IsLocalRing.residue_eq_zero_iff r).2 hr, zero_mul]⟩
  have hinj : Function.Injective (fun φ : A →ₗ[Λ] IsLocalRing.ResidueField Λ =>
      (F.map (ModuleCat.ofHom φ : A ⟶ ModuleCat.of Λ (IsLocalRing.ResidueField Λ))).hom x) := by
    intro φ ψ h
    have := hmin (ModuleCat.of Λ (IsLocalRing.ResidueField Λ)) hk
      ((ModuleCat.ofHom φ : A ⟶ ModuleCat.of Λ (IsLocalRing.ResidueField Λ)) - ModuleCat.ofHom ψ) (by
        rw [F.map_sub]
        exact sub_eq_zero.2 h)
    have h2 := sub_eq_zero.1 this
    exact congrArg ModuleCat.Hom.hom h2
  have h1 : Nat.card (A →ₗ[Λ] IsLocalRing.ResidueField Λ) ≤ c := Nat.card_le_card_of_injective _ hinj
  have h2 : c ≤ Nat.card (IsLocalRing.ResidueField Λ) ^ c :=
    (Nat.lt_pow_self Finite.one_lt_card).le
  obtain ⟨v, hv⟩ := GlobalTheory.T.exists_generators_of_card_hom_residueField_le Λ A c (h1.trans h2)
  let p : Fin c → (Λ ⧸ IsLocalRing.maximalIdeal Λ ^ n) →ₗ[Λ] A := fun i =>
    (IsLocalRing.maximalIdeal Λ ^ n).liftQ (LinearMap.toSpanSingleton Λ A (v i)) (fun r hr => hn r hr _)
  refine Nat.card_le_card_of_surjective (fun t => ∑ i, p i (t i)) (fun a => ?_)
  have ha : a ∈ Submodule.span Λ (Set.range v) := hv ▸ Submodule.mem_top
  obtain ⟨t, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun Λ).1 ha
  exact ⟨fun i => Submodule.Quotient.mk (t i), rfl⟩

theorem level : ∀ (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [Finite (IsLocalRing.ResidueField Λ)]
  (F : ModuleCat.{0} Λ ⥤ ModuleCat.{0} Λ) [F.Additive] [F.Linear Λ],
  (∀ (B' B B'' : ModuleCat.{0} Λ), Tors Λ B → Tors Λ B'' → ∀ (f : B' ⟶ B) (g : B ⟶ B''), Function.Injective f.hom →
      Function.Exact f.hom g.hom → Function.Injective (F.map f).hom ∧ Function.Exact (F.map f).hom (F.map g).hom) →
  Finite (F.obj (ModuleCat.of Λ (IsLocalRing.ResidueField Λ))) → ∀ n : ℕ,
  ∃ (M : ModuleCat.{0} Λ) (ξ : F.obj M), Finite M ∧ (∀ x ∈ IsLocalRing.maximalIdeal Λ ^ n, ∀ y : M, x • y = 0) ∧
    (∀ B : ModuleCat.{0} Λ, Tors Λ B → ∀ φ : M ⟶ B, (F.map φ).hom ξ = 0 → φ = 0) ∧
    ∀ B : ModuleCat.{0} Λ, Finite B → (∀ x ∈ IsLocalRing.maximalIdeal Λ ^ n, ∀ y : B, x • y = 0) →
      ∀ η : F.obj B, ∃ φ : M ⟶ B, (F.map φ).hom ξ = η := by
  classical
  intro Λ _ _ _ _ F _ _ hF hfin n
  obtain ⟨N, hN⟩ := card_le_of_min F hfin n
  let P : ℕ → Prop := fun m => ∃ (M : ModuleCat.{0} Λ) (ξ : F.obj M), Finite M ∧
    (∀ x ∈ IsLocalRing.maximalIdeal Λ ^ n, ∀ y : M, x • y = 0) ∧ IsMin F M ξ ∧ Nat.card M = m
  have h0 : P (Nat.card (ModuleCat.of Λ PUnit)) :=
    ⟨ModuleCat.of Λ PUnit, 0, inferInstanceAs (Finite PUnit), fun _ _ _ => rfl, fun B _ φ _ => by
      ext c
      exact map_zero φ.hom, rfl⟩
  have hle : ∀ m, P m → m ≤ N := by
    rintro m ⟨M, ξ, h1, h2, h3, rfl⟩
    exact hN M ξ h1 h2 h3
  obtain ⟨M, ξ, hM, hMn, hmin, hcard⟩ : P (Nat.findGreatest P N) := Nat.findGreatest_spec (hle _ h0) h0
  refine ⟨M, ξ, hM, hMn, hmin, fun B hB hBn η => ?_⟩
  let A : ModuleCat.{0} Λ := ModuleCat.of Λ (M × B)
  haveI : Finite A := inferInstanceAs (Finite (M × B))
  have hAn : ∀ x ∈ IsLocalRing.maximalIdeal Λ ^ n, ∀ y : A, x • y = 0 := fun r hr y =>
    Prod.ext (hMn r hr y.1) (hBn r hr y.2)
  let i1 : M ⟶ A := ModuleCat.ofHom (LinearMap.inl Λ M B)
  let i2 : B ⟶ A := ModuleCat.ofHom (LinearMap.inr Λ M B)
  let q1 : A ⟶ M := ModuleCat.ofHom (LinearMap.fst Λ M B)
  let q2 : A ⟶ B := ModuleCat.ofHom (LinearMap.snd Λ M B)
  have e11 : i1 ≫ q1 = 𝟙 M := rfl
  have e22 : i2 ≫ q2 = 𝟙 B := rfl
  have e12 : i1 ≫ q2 = 0 := rfl
  have e21 : i2 ≫ q1 = 0 := rfl
  obtain ⟨C, f, z, hf, hz, hC⟩ := exists_min F hF A (fun a => ⟨n, fun r hr => hAn r hr a⟩)
    ((F.map i1).hom ξ + (F.map i2).hom η)
  have hz1 : (F.map (f ≫ q1)).hom z = ξ := by
    rw [← map_map, hz, map_add, map_map, map_map, e11, e21, F.map_id, F.map_zero]
    exact add_zero _
  have hz2 : (F.map (f ≫ q2)).hom z = η := by
    rw [← map_map, hz, map_add, map_map, map_map, e12, e22, F.map_id, F.map_zero]
    exact zero_add _
  haveI hCf : Finite C := Finite.of_injective _ hf
  set g := f ≫ q1 with hg
  have hsurj : Function.Surjective g.hom := by
    have := hmin (ModuleCat.of Λ (M ⧸ LinearMap.range g.hom)) (fun b => ⟨n, fun r hr => by
      obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ b
      rw [← Submodule.Quotient.mk_smul, hMn r hr, Submodule.Quotient.mk_zero]⟩)
      (ModuleCat.ofHom (LinearMap.range g.hom).mkQ) (by
        have e : g ≫ ModuleCat.ofHom (LinearMap.range g.hom).mkQ = 0 := by
          ext c
          exact (Submodule.Quotient.mk_eq_zero _).2 ⟨c, rfl⟩
        rw [← hz1, map_map, e, F.map_zero]
        rfl)
    intro m
    have h3 : (LinearMap.range g.hom).mkQ m = 0 :=
      congrArg (fun φ : M ⟶ ModuleCat.of Λ (M ⧸ LinearMap.range g.hom) => φ.hom m) this
    exact (Submodule.Quotient.mk_eq_zero _).1 h3
  have hPC : P (Nat.card C) := ⟨C, z, hCf, fun r hr y => hf (by rw [map_smul, hAn r hr, map_zero]), hC, rfl⟩
  have hcle : Nat.card C ≤ Nat.card M := hcard ▸ Nat.le_findGreatest (hle _ hPC) hPC
  have hbij : Function.Bijective g.hom := hsurj.bijective_of_nat_card_le hcle
  let e := LinearEquiv.ofBijective g.hom hbij
  refine ⟨(ModuleCat.ofHom e.symm.toLinearMap : M ⟶ C) ≫ f ≫ q2, ?_⟩
  have e3 : g ≫ (ModuleCat.ofHom e.symm.toLinearMap : M ⟶ C) = 𝟙 C := by
    ext c
    exact e.symm_apply_apply c
  rw [← hz1, map_map, ← Category.assoc, e3, Category.id_comp, hz2]

end GlobalTheory.SelFun.Level
