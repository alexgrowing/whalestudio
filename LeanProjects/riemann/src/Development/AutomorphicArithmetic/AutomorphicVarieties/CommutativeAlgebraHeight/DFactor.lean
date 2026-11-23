import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.OfDetToDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

section
variable {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) {E' : Type} [Ring E'] [Algebra A E']
  (f : E →ₐ[A] E')

private theorem map_eq_lTensor (S : Type) [CommRing S] [Algebra A S] (z : S ⊗[A] E) :
    Algebra.TensorProduct.map (AlgHom.id S S) f z = f.toLinearMap.lTensor S z := by
  induction z with
  | zero => simp
  | tmul s x => simp
  | add a b ha hb => simp only [map_add, ha, hb]

private theorem map_surj (hf : Function.Surjective f) (S : Type) [CommRing S] [Algebra A S] :
    Function.Surjective (Algebra.TensorProduct.map (AlgHom.id S S) f) := by
  intro y
  obtain ⟨x, hx⟩ := LinearMap.lTensor_surjective S (g := f.toLinearMap) hf y
  exact ⟨x, (map_eq_lTensor f S x).trans hx⟩

private theorem eq_of_map_eq (hf : Function.Surjective f) (hk : ∀ x, f x = 0 → x ∈ D.ker)
    (S : Type) [CommRing S] [Algebra A S] (x y : S ⊗[A] E)
    (h : Algebra.TensorProduct.map (AlgHom.id S S) f x = Algebra.TensorProduct.map (AlgHom.id S S) f y) :
    D.D S x = D.D S y := by
  have hex := lTensor_exact S (LinearMap.exact_subtype_ker_map f.toLinearMap) hf
  have h0 : f.toLinearMap.lTensor S (x - y) = 0 := by
    rw [← map_eq_lTensor, map_sub, h, sub_self]
  obtain ⟨w, hw⟩ := (hex _).1 h0
  have key : ∀ (w : S ⊗[A] (LinearMap.ker f.toLinearMap)) (y : S ⊗[A] E),
      D.D S (y + (LinearMap.ker f.toLinearMap).subtype.lTensor S w) = D.D S y := by
    intro w
    induction w with
    | zero => simp
    | tmul s k =>
      intro y
      have := (D.mem_ker.1 (hk k.1 k.2)) S y (s ⊗ₜ 1) 1
      simpa using this
    | add a b ha hb => intro y; rw [LinearMap.map_add, ← add_assoc, hb, ha]
  rw [← key w y, hw, add_sub_cancel]

private theorem map_map_swap (B B' : Type) [CommRing B] [Algebra A B] [CommRing B'] [Algebra A B'] (g : B →ₐ[A] B')
    (x : B ⊗[A] E) :
    Algebra.TensorProduct.map (AlgHom.id B' B') f (Algebra.TensorProduct.map g (AlgHom.id A E) x) =
      Algebra.TensorProduct.map g (AlgHom.id A E') (Algebra.TensorProduct.map (AlgHom.id B B) f x) := by
  induction x with
  | zero => simp
  | tmul s x => simp
  | add a b ha hb => simp only [map_add, ha, hb]

end

theorem UpperTheory.V.CA.d_factor :
    ∀ {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) {E' : Type} [Ring E'] [Algebra A E'] (f : E →ₐ[A] E'), Function.Surjective f → (∀ x, f x = 0 → x ∈ D.ker) → ∃! D' : Det n A E', D'.pull f = D := by
  intro n A E _ _ _ D E' _ _ f hf hk
  have hs := map_surj f hf
  have he := eq_of_map_eq D f hf hk
  have hσ : ∀ (S : Type) [CommRing S] [Algebra A S] (x : S ⊗[A] E),
      D.D S (Function.surjInv (hs S) (Algebra.TensorProduct.map (AlgHom.id S S) f x)) = D.D S x :=
    fun S _ _ x => he S _ _ (Function.surjInv_eq _ _)
  let D' : Det n A E' :=
    { D := fun S _ _ =>
        { toFun := fun y => D.D S (Function.surjInv (hs S) y)
          map_one' := by
            rw [← map_one (Algebra.TensorProduct.map (AlgHom.id S S) f), hσ, map_one]
          map_mul' := fun x y => by
            obtain ⟨x, rfl⟩ := hs S x
            obtain ⟨y, rfl⟩ := hs S y
            rw [← map_mul (Algebra.TensorProduct.map (AlgHom.id S S) f), hσ, hσ, hσ, map_mul] }
      nat := fun B B' _ _ _ _ g x => by
        obtain ⟨x, rfl⟩ := hs B x
        change D.D B' (Function.surjInv (hs B') _) = g (D.D B (Function.surjInv (hs B) _))
        rw [← map_map_swap, hσ, hσ, D.nat]
      homog := fun B _ _ b x => by
        obtain ⟨x, rfl⟩ := hs B x
        change D.D B (Function.surjInv (hs B) _) = b ^ n * D.D B (Function.surjInv (hs B) _)
        rw [← map_smul, hσ, hσ, D.homog] }
  refine ⟨D', Det.ext' fun S _ _ x => hσ S x, fun D'' h => Det.ext' fun S _ _ y => ?_⟩
  obtain ⟨x, rfl⟩ := hs S y
  refine Eq.trans ?_ (hσ S x).symm
  rw [← h]
  rfl
