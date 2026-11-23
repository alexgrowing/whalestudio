import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.XSmulSucc
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.FibInit
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.FBnat

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Polynomial CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
universe w w' v u v' u' v'' u''

namespace CrystallineSemistableComparison.B

theorem kstep_aug_d {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{w} R)
    {M : Type w'} [AddCommGroup M] [Module R M] (e : ∀ T : C, M →ₗ[R] F.obj T)
    (he : ∀ {T T' : C} (φ : T ⟶ T') x, (F.map φ).hom (e T x) = e T' x) (x : M) :
    d F 0 (aug F e x) = 0 := by
  funext s
  change ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • (F.map (GlobalTheory.CatH.toLast i s)).hom (e _ x) = 0
  simp only [he, Fin.sum_univ_two]
  simp

def kstepLast (d k : ℕ) : Gam (d + 1) := Multiplicative.ofAdd (Pi.single (Fin.last d) k)

section kstep

variable {d : ℕ} (π : Gam (d + 1) →* Gam d)
  (hπ : ∀ a k, Multiplicative.toAdd (π a) k = Multiplicative.toAdd a k.castSucc)

include hπ in
theorem kstep_π_last (k : ℕ) : π (kstepLast d k) = 1 := by
  apply Multiplicative.toAdd.injective
  funext i
  rw [hπ]
  simp [kstepLast, Fin.castSucc_ne_last]

def kstepL (hπ : ∀ a k, Multiplicative.toAdd (π a) k = Multiplicative.toAdd a k.castSucc) : SingleObj (Multiplicative ℕ) ⥤ StructuredArrow (SingleObj.star (Gam d)) π.toFunctor where
  obj _ := StructuredArrow.mk (Y := SingleObj.star (Gam (d + 1)))
    (show SingleObj.star (Gam d) ⟶ π.toFunctor.obj (SingleObj.star _) from (1 : Gam d))
  map k := StructuredArrow.homMk (show SingleObj.star (Gam (d + 1)) ⟶ SingleObj.star _ from
      kstepLast d (Multiplicative.toAdd k)) (by
    simp only [StructuredArrow.mk_hom_eq_self]
    exact kstep_π_last π hπ _)
  map_id _ := by
    apply StructuredArrow.hom_ext
    change kstepLast d (Multiplicative.toAdd (1 : Multiplicative ℕ)) = (1 : Gam (d + 1))
    simp [kstepLast]
  map_comp f g := by
    apply StructuredArrow.hom_ext
    change kstepLast d (Multiplicative.toAdd ((show Multiplicative ℕ from g) * (show Multiplicative ℕ from f))) = kstepLast d (Multiplicative.toAdd (g : Multiplicative ℕ)) * kstepLast d (Multiplicative.toAdd (f : Multiplicative ℕ))
    simp [kstepLast, Pi.single_add]

def kstepU : StructuredArrow (SingleObj.star (Gam d)) π.toFunctor ⥤ SingleObj (Multiplicative ℕ) where
  obj _ := SingleObj.star _
  map f := Multiplicative.ofAdd (Multiplicative.toAdd (f.right : Gam (d + 1)) (Fin.last d))
  map_id _ := by
    change Multiplicative.ofAdd (Multiplicative.toAdd (1 : Gam (d + 1)) (Fin.last d)) = 1
    simp
  map_comp f g := by
    change Multiplicative.ofAdd (Multiplicative.toAdd ((show Gam (d + 1) from g.right) * (show Gam (d + 1) from f.right)) (Fin.last d)) =
      Multiplicative.ofAdd (Multiplicative.toAdd (g.right : Gam (d + 1)) (Fin.last d)) *
        Multiplicative.ofAdd (Multiplicative.toAdd (f.right : Gam (d + 1)) (Fin.last d))
    simp only [toAdd_mul, Pi.add_apply, ofAdd_add]
    rfl

def kstepSnoc (b : Gam d) (k : ℕ) : Gam (d + 1) :=
  Multiplicative.ofAdd (Fin.snoc (α := fun _ => ℕ) (Multiplicative.toAdd b) k)

include hπ in
theorem kstep_π_snoc (b : Gam d) (k : ℕ) : π (kstepSnoc b k) = b := by
  apply Multiplicative.toAdd.injective
  funext i
  rw [hπ]
  simp [kstepSnoc]

include hπ in
theorem kstep_snoc_eq (a : Gam (d + 1)) : kstepSnoc (π a) (Multiplicative.toAdd a (Fin.last d)) = a := by
  apply Multiplicative.toAdd.injective
  funext i
  induction i using Fin.lastCases with
  | last => simp [kstepSnoc]
  | cast i => simp [kstepSnoc, hπ]

def kstepAdj : kstepL π hπ ⊣ kstepU π :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f => show X ⟶ (kstepU π).obj Y from
            Multiplicative.ofAdd (Multiplicative.toAdd (f.right : Gam (d + 1)) (Fin.last d))
          invFun := fun k => StructuredArrow.homMk
            (show ((kstepL π hπ).obj X).right ⟶ Y.right from
              kstepSnoc (show Gam d from Y.hom) (Multiplicative.toAdd (show Multiplicative ℕ from k)))
            (kstep_π_snoc π hπ _ _)
          left_inv := fun f => by
            apply StructuredArrow.hom_ext
            change kstepSnoc (show Gam d from Y.hom) (Multiplicative.toAdd (f.right : Gam (d + 1)) (Fin.last d)) = f.right
            have w : (show Gam d from Y.hom) = π f.right := (StructuredArrow.w f).symm
            rw [w]
            exact kstep_snoc_eq π hπ _
          right_inv := fun k => by
            change Multiplicative.ofAdd (Multiplicative.toAdd
              (kstepSnoc (show Gam d from Y.hom) (Multiplicative.toAdd (show Multiplicative ℕ from k))) (Fin.last d)) = k
            simp [kstepSnoc] }
      homEquiv_naturality_left_symm := fun {X' X Y} f g => by
        apply StructuredArrow.hom_ext
        change kstepSnoc (show Gam d from Y.hom)
            (Multiplicative.toAdd ((show Multiplicative ℕ from g) * (show Multiplicative ℕ from f))) =
          kstepSnoc (show Gam d from Y.hom) (Multiplicative.toAdd (show Multiplicative ℕ from g)) *
            kstepLast d (Multiplicative.toAdd (show Multiplicative ℕ from f))
        apply Multiplicative.toAdd.injective
        funext i
        induction i using Fin.lastCases with
        | last => simp [kstepSnoc, kstepLast]
        | cast i => simp [kstepSnoc, kstepLast, Fin.castSucc_ne_last]
      homEquiv_naturality_right := fun f g => (kstepU π).map_comp f g }

end kstep

end CrystallineSemistableComparison.B

theorem CrystallineSemistableComparison.B.P.kstep : ∀ {R : Type} [CommRing R] {d : ℕ} (M : SingleObj (Gam d) ⥤ ModuleCat.{w} R) (N : SingleObj (Gam (d + 1)) ⥤ ModuleCat.{w} R) (π : Gam (d + 1) →* Gam d) (hπ : ∀ a k, Multiplicative.toAdd (π a) k = Multiplicative.toAdd a k.castSucc) (τ : M.obj (SingleObj.star _) →ₗ[R] N.obj (SingleObj.star _)) (h : ∀ (a : Gam (d + 1)) x, τ ((M.map (X := SingleObj.star _) (Y := SingleObj.star _) (π a)).hom x) = (N.map (X := SingleObj.star _) (Y := SingleObj.star _) a).hom (τ x)) (s : R), Acyc1 s τ (N.map (X := SingleObj.star _) (Y := SingleObj.star _) (gen (Fin.last d))).hom → ∀ n, IsoLe (s ^ (2 * n + 3)) n (⟨π.toFunctor, fun _ => τ, fun φ x => h φ x⟩ : Mor M N (RingHom.id R)) := by
  intro R _ d M N π hπ τ h s hA n
  apply CrystallineSemistableComparison.B.P.fib
  intro T
  have hM1 : M.map (X := SingleObj.star _) (Y := SingleObj.star _) (1 : Gam d) = 𝟙 _ := M.map_id _
  obtain rfl : T = SingleObj.star (Gam d) := Subsingleton.elim _ _
  let F' : StructuredArrow (SingleObj.star (Gam d)) π.toFunctor ⥤ ModuleCat.{w} R :=
    StructuredArrow.proj (SingleObj.star (Gam d)) π.toFunctor ⋙ N
  let e : ∀ x : StructuredArrow (SingleObj.star (Gam d)) π.toFunctor,
      M.obj (SingleObj.star (Gam d)) →ₗ[R] F'.obj x := fun x => τ ∘ₗ (M.map x.hom).hom
  have he : ∀ {x y : StructuredArrow (SingleObj.star (Gam d)) π.toFunctor} (φ : x ⟶ y) a,
      (F'.map φ).hom (e x a) = e y a := by
    intro x y φ a
    have h1 := h φ.right ((M.map x.hom).hom a)
    refine h1.symm.trans ?_
    change τ ((M.map x.hom ≫ M.map (π.toFunctor.map φ.right)).hom a) = τ ((M.map y.hom).hom a)
    rw [← M.map_comp, StructuredArrow.w φ]
  have hfix : ∀ x, (N.map (X := SingleObj.star _) (Y := SingleObj.star _) (gen (Fin.last d))).hom (τ x) = τ x := by
    intro x
    rw [← h, show π (gen (Fin.last d)) = 1 from kstep_π_last π hπ 1, hM1]
    rfl
  have hb := CrystallineSemistableComparison.B.P.bnat (kstepL π hπ ⋙ F') τ s hfix hA
  have hadj := CrystallineSemistableComparison.P.adj F' (kstepL π hπ) (kstepU π) (kstepAdj π hπ)
  have hup : ∀ k, UpTo (1 : R) ((Mor.restrict F' (kstepL π hπ)).hom.mapH k) := fun k =>
    ((CrystallineSemistableComparison.P.upTo_alg _ (LinearMap.id (R := R)) (1 : R) 1).2.2.2.2).2 (hadj k)
  have hε : (Mor.restrict F' (kstepL π hπ)).hom.f 0 ∘ₗ aug F' e = aug (kstepL π hπ ⋙ F') fun _ => τ := by
    refine LinearMap.ext fun x => funext fun s => ?_
    change τ ((M.map (1 : Gam d)).hom x) = τ x
    rw [hM1]
    rfl
  have htr := (CrystallineSemistableComparison.P.res_transfer (Mor.restrict F' (kstepL π hπ)).hom (aug F' e) s 1 hup).2
    (kstep_aug_d F' e he) (hε ▸ hb)
  rw [mul_one] at htr
  exact htr
