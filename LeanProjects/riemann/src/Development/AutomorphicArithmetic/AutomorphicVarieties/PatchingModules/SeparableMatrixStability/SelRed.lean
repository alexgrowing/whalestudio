import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.MapEta
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SelMap

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

section

variable {A X X' : Type} [CommRing A] [CommRing X] [Algebra A X] [CommRing X'] [Algebra A X'] (f : X →ₐ[A] X') {n : ℕ}

private theorem map_alg (M : Matrix (Fin n) (Fin n) A) :
    (M.map (algebraMap A X)).map f = M.map (algebraMap A X') := by
  ext i j; simp

private theorem map_mul_alg (M N : Matrix (Fin n) (Fin n) X) : (M * N).map f = M.map f * N.map f :=
  map_mul f.mapMatrix M N

private theorem map_add_one (M : Matrix (Fin n) (Fin n) X) : (1 + M).map f = 1 + M.map f := by
  rw [Matrix.map_add _ (map_add f), Matrix.map_one _ (map_zero f) (map_one f)]

private theorem map_sub_one (M : Matrix (Fin n) (Fin n) X) : (1 - M).map f = 1 - M.map f := by
  rw [Matrix.map_sub _ (map_sub f), Matrix.map_one _ (map_zero f) (map_one f)]

private theorem map_epM {g : ℕ} (Z : Fin g → Matrix (Fin n) (Fin n) A) :
    (DD.epM fun j => (Z j).map (algebraMap A X)).map (DD.map g f) = DD.epM fun j => (Z j).map (algebraMap A X') := by
  ext i j <;> simp [DD.epM, DD.map]

private theorem blk_map (a : ℕ) (V₁ V₂ : Submodule A X) (V₁' V₂' : Submodule A X')
    (h₁ : ∀ y ∈ V₁, f y ∈ V₁') (h₂ : ∀ y ∈ V₂, f y ∈ V₂') :
    ∀ Z ∈ blkMat n a V₁ V₂, Z.map f ∈ blkMat n a V₁' V₂' :=
  fun _ hZ i j => ⟨fun e => h₁ _ ((hZ i j).1 e), fun e => h₂ _ ((hZ i j).2 e)⟩

private theorem part_map (g : ℕ) (b₁ b₂ b₃ b₄ : Bool) :
    ∀ y ∈ ddPart A X g b₁ b₂ b₃ b₄, DD.map g f y ∈ ddPart A X' g b₁ b₂ b₃ b₄ := by
  rintro y ⟨ha, hep, hep', heta⟩
  refine ⟨fun hb => ?_, fun hb => ?_, fun hb => ?_, fun hb => ?_⟩
  · show f y.a = 0
    rw [ha hb, map_zero]
  · show (fun j => f (y.ep j)) = 0
    funext j
    rw [hep hb]
    simp
  · show (fun j => f (y.ep' j)) = 0
    funext j
    rw [hep' hb]
    simp
  · show f y.eta = 0
    rw [heta hb, map_zero]

end

theorem UpperTheory.V.Pa.sel_red :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (k : Kap x) (X X' : Type) [CommRing X] [Algebra x.A X] [CommRing X'] [Algebra x.A X'] (f : X →ₐ[x.A] X'), (∀ z ∈ SelP h x X, (fun g => (z g).map f) ∈ SelP h x X') ∧ (∀ z ∈ Sel1 h X k, (fun g => (z g).map (DD.map k.g f)) ∈ Sel1 h X' k) ∧ (∀ z ∈ Sel2 h X k, (fun g => (z g).map (DD.map k.g f)) ∈ Sel2 h X' k) ∧ (∀ g, (k.ρ1 X g).map (DD.map k.g f) = k.ρ1 X' g) ∧ ∀ v, (k.w1 X v).map (DD.map k.g f) = k.w1 X' v ∧ (k.wi1 X v).map (DD.map k.g f) = k.wi1 X' v := by
  intro l _ L G G0 h n x k X X' _ _ _ _ f
  have hρ1 : ∀ g, (k.ρ1 X g).map (DD.map k.g f) = k.ρ1 X' g := by
    intro g
    unfold Kap.ρ1 NP.ρX
    rw [map_mul_alg, map_add_one, map_epM, map_alg]
  have hw1 : ∀ v, (k.w1 X v).map (DD.map k.g f) = k.w1 X' v := by
    intro v
    unfold Kap.w1 NP.wX
    rw [map_mul_alg, map_sub_one, map_epM, map_alg]
  have hwi1 : ∀ v, (k.wi1 X v).map (DD.map k.g f) = k.wi1 X' v := by
    intro v
    unfold Kap.wi1 NP.wiX
    rw [map_mul_alg, map_add_one, map_epM, map_alg]
  refine ⟨fun z hz => ?_, fun z hz => ?_, fun z hz => ?_, hρ1, fun v => ⟨hw1 v, hwi1 v⟩⟩
  · have hV : ∀ Z ∈ Ev x.A X n x.a, Z.map f ∈ Ev x.A X' n x.a :=
      blk_map f x.a ⊤ ⊥ ⊤ ⊥ (fun _ _ => Submodule.mem_top) (fun y hy => by
        rw [Submodule.mem_bot] at hy ⊢
        rw [hy, map_zero])
    have H := (sel_map l G.frame n x.A X X' f x.t (fun g => x.ρX X (h.p₀ g)) (x.wX X) (x.wiX X) _ _ hV z).1 hz
    simp only [NP.ρX, NP.wX, NP.wiX, map_alg] at H
    exact H
  · have hV : ∀ Z ∈ W1 n x.A X k.g x.a, Z.map (DD.map k.g f) ∈ W1 n x.A X' k.g x.a :=
      blk_map (DD.map k.g f) x.a _ _ _ _ (part_map f k.g _ _ _ _) (part_map f k.g _ _ _ _)
    have H := (sel_map l G.frame n x.A (DD X k.g) (DD X' k.g) (DD.map k.g f) x.t
      (fun g => k.ρ1 X (h.p₀ g)) (k.w1 X) (k.wi1 X) _ _ hV z).1 hz
    simp only [hρ1, hw1, hwi1] at H
    exact H
  · have hV : ∀ Z ∈ W2 n x.A X k.g x.a, Z.map (DD.map k.g f) ∈ W2 n x.A X' k.g x.a :=
      blk_map (DD.map k.g f) x.a _ _ _ _ (part_map f k.g _ _ _ _) (part_map f k.g _ _ _ _)
    have H := (sel_map l G.frame n x.A (DD X k.g) (DD X' k.g) (DD.map k.g f) x.t
      (fun g => k.ρ1 X (h.p₀ g)) (k.w1 X) (k.wi1 X) _ _ hV z).1 hz
    simp only [hρ1, hw1, hwi1] at H
    exact H
