import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.IsLocPres

noncomputable section

namespace UpperTheory.V.U3

open Matrix IsLocalRing UpperTheory.V.Alg

def form6 (O : Type) [CommRing O] : FormData O wt6 where
  J := Matrix.fromBlocks 0 (Jmat O 3) (Jmat O 3) 0
  unit := IsUnit.of_mul_eq_one (Matrix.fromBlocks 0 (Jmat O 3) (Jmat O 3) 0) (by
    simp [Matrix.fromBlocks_multiply, Jmat_mul_Jmat])
  sym := Or.inl (by simp [Matrix.fromBlocks_transpose, Jmat_transpose])
  κ := Bool
  blk := Sum.isLeft
  σ := not
  invol := Bool.not_not
  hblk a b h := by
    rcases a with a | a <;> rcases b with b | b <;> simp at h ⊢
  c := 0
  hw a b h := by
    rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;> simp [Jmat] at h <;> first | rfl | exact absurd rfl h

theorem blockPairingForm_JR (O R : Type) [CommRing O] [CommRing R] [Algebra O R] :
    (form6 O).JR R = Matrix.fromBlocks 0 (Jmat R 3) (Jmat R 3) 0 := by
  simp [FormData.JR, form6, Matrix.fromBlocks_map, Jmat_map]

theorem emb_apply {m : ℕ} {R : Type*} [CommRing R] (x : GG m R) :
    emb x = if x.right = 1 then Matrix.fromBlocks x.mat 0 0 (theta x.left : GL (Fin m) R)
      else Matrix.fromBlocks 0 x.mat (theta x.left : GL (Fin m) R) 0 := rfl

theorem emb_map' {m : ℕ} {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (x : GG m R) :
    emb (GG.map f x) = (emb x).map f := by
  have h : (theta (GG.map f x).left : Matrix (Fin m) (Fin m) S) = (theta x.left : Matrix (Fin m) (Fin m) R).map f :=
    (congrArg Units.val (map_theta f x.left)).symm
  rw [emb_apply, emb_apply, h, GG.map_mat, GG.map_right]
  split_ifs <;> simp [Matrix.fromBlocks_map]

theorem mat_eq_emb' {m : ℕ} {R : Type*} [CommRing R] (x : GG m R) (a b : Fin m) :
    x.mat a b = emb x (.inl a) (.inl b) + emb x (.inl a) (.inr b) := by
  rw [emb_apply]
  split_ifs <;> simp

theorem eq_of_emb {m : ℕ} {R : Type*} [CommRing R] {x y : GG m R} (h : x.right = y.right) (e : emb x = emb y) :
    x = y := by
  refine SemidirectProduct.ext (Units.ext ?_) h
  ext a b
  exact (mat_eq_emb' x a b).trans (e ▸ (mat_eq_emb' y a b).symm)

theorem emb_form (O : Type) [CommRing O] {R : Type} [CommRing R] [Algebra O R] (x : GG 3 R) :
    (emb x)ᵀ * (form6 O).JR R * emb x = (form6 O).JR R := by
  have h1 : x.matᵀ * Jmat R 3 * (theta x.left : GL (Fin 3) R) = Jmat R 3 := by
    rw [theta_val, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc _ (Jmat R 3) (Jmat R 3), Jmat_mul_Jmat,
      Matrix.mul_one, GG.mat, ← Matrix.transpose_mul]
    simp
  have h2 : ((theta x.left : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R)ᵀ * Jmat R 3 * x.mat = Jmat R 3 := by
    have := congrArg Matrix.transpose h1
    rwa [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Jmat_transpose,
      ← Matrix.mul_assoc] at this
  rw [blockPairingForm_JR, emb_apply]
  split_ifs <;> simp [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, h1, h2]

theorem emb_blk {m : ℕ} {R : Type*} [CommRing R] (x : GG m R) (a b : Fin m ⊕ Fin m) (h : emb x a b ≠ 0) :
    a.isLeft = if x.right = 1 then b.isLeft else !b.isLeft := by
  rw [emb_apply] at h
  split_ifs at h ⊢ <;> rcases a with a | a <;> rcases b with b | b <;> simp at h ⊢

theorem unitaryGroupEmbedding_baseLift_eq_zero_of_wt_ne {G R : Type} [Group G] [CommRing R] (η : G →* ℤˣ) (Ψ : G →* Rˣ) (g : G)
    (a b : Fin 3 ⊕ Fin 3) (h : wt6 a ≠ wt6 b) : emb (r0 η Ψ g) a b = 0 := by
  rw [emb_apply, GG.mat, unitaryThreeReflection_left, theta_tor, tor_val]
  split_ifs <;> rcases a with a | a <;> rcases b with b | b <;>
    first
    | rfl
    | exact Matrix.diagonal_apply_ne (i := a) (j := b) (fun i => ((Ψ g ^ wt1 i : Rˣ) : R)) (by rintro rfl; exact h rfl)

def sgnPerm : ℤˣ →* Equiv.Perm Bool where
  toFun s := if s = 1 then 1 else Function.Involutive.toPerm not Bool.not_not
  map_one' := if_pos rfl
  map_mul' s t := by
    rcases Int.units_eq_one_or s with rfl | rfl <;> rcases Int.units_eq_one_or t with rfl | rfl <;> decide

theorem blockPairingForm_normalises_baseLift (O : Type) [CommRing O] {G R : Type} [Group G] [CommRing R] [Algebra O R] (η : G →* ℤˣ)
    (Ψ : G →* Rˣ) : (form6 O).Normalises (emb.comp (r0 η Ψ)) := by
  refine ⟨fun g => ⟨1, by rw [one_smul]; exact emb_form O _⟩, ⟨sgnPerm.comp η, fun g a b h => ?_⟩,
    fun g a b h => unitaryGroupEmbedding_baseLift_eq_zero_of_wt_ne η Ψ g a b h⟩
  have := emb_blk _ a b h
  show a.isLeft = (if η g = 1 then 1 else Function.Involutive.toPerm not Bool.not_not : Equiv.Perm Bool) b.isLeft
  rw [this, unitaryThreeReflection_right]
  split_ifs <;> rfl

variable {O : Type} [CommRing O] [IsLocalRing O] {Γ : Type} [Group Γ] [TopologicalSpace Γ] {η : Γ →* ℤˣ}
  {Ψ : Γ →* Oˣ} {R : Type} [CommRing R] [Algebra O R] [IsCO O R]

theorem baseLift_map_residue {G : Type} [Group G] (η : G →* ℤˣ) (Ψ : G →* Oˣ) (g : G) :
    GG.map (residue O) (r0 η Ψ g) = rbar O η Ψ g := by
  refine SemidirectProduct.ext (Units.ext ?_) rfl
  show (tor O (Ψ g) : Matrix (Fin 3) (Fin 3) O).map (residue O) = tor _ (barChar O Ψ g)
  rw [tor_val, tor_val, Matrix.diagonal_map (map_zero _)]
  congr 1
  funext i
  exact congrArg Units.val (map_zpow (Units.map (residue O).toMonoidHom) (Ψ g) (wt1 i))

theorem GLift.locConst (hη : IsLocallyConstant η) (r : GLift O η Ψ R) (n : ℕ) :
    IsLocallyConstant fun g => GG.map (Ideal.Quotient.mk (maximalIdeal R ^ n)) (r.hom g) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have h1 := (IsLocallyConstant.iff_eventually_eq _).1 hη x
  have h2 : ∀ᶠ y in nhds x, ∀ a b, Ideal.Quotient.mk (maximalIdeal R ^ n) ((r.hom y).mat a b) =
      Ideal.Quotient.mk (maximalIdeal R ^ n) ((r.hom x).mat a b) :=
    Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun b =>
      (IsLocallyConstant.iff_eventually_eq _).1 (r.cont a b n) x
  filter_upwards [h1, h2] with y e1 e2
  refine SemidirectProduct.ext (Units.ext ?_) ((r.hasMult y).trans (e1.trans (r.hasMult x).symm))
  ext a b
  exact e2 a b

def GLift.toLift (hη : IsLocallyConstant η) (r : GLift O η Ψ R) : Lift O (emb.comp (rbar O η Ψ)) R where
  hom := emb.comp r.hom
  cont a b n := by
    have := (r.locConst hη n).comp fun x => emb x a b
    simpa only [Function.comp_def, emb_map', Matrix.map_apply, MonoidHom.comp_apply] using this
  red g a b := by
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, ← r.red g, emb_map']
    rfl

abbrev unitFrame {G H : Type} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H] (π : G →* Γ)
    (hπ : Continuous π) (ι : H →* G) (hι : Continuous ι) {Q : Type} [Fintype Q] (D : Q → Subgroup G)
    (N : Q → Subgroup G) : Frame Γ where
  T := Unit
  v0 := ()
  Gv _ := H
  φ _ := π.comp ι
  hφ _ := hπ.comp hι
  Q := Q
  Gq q := D q
  ψ q := π.comp (D q).subtype
  hψ _ := hπ.comp continuous_subtype_val
  N q := (N q).subgroupOf (D q)

abbrev adBar (O : Type) [CommRing O] [IsLocalRing O] {G : Type} [Group G] (η : G →* ℤˣ) (Ψ : G →* Oˣ) (j : ℤ) :
    Representation (ResidueField O) G ((form6 O).gw (ResidueField O) j) :=
  FormData.adRep (ρ := emb.comp (rbar O η Ψ)) (blockPairingForm_normalises_baseLift O η (barChar O Ψ)) j

end UpperTheory.V.U3
