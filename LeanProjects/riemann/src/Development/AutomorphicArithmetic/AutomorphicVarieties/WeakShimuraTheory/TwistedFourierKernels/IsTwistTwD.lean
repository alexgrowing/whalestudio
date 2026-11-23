import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ArithmeticPointClassicality

noncomputable section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W

namespace UpperTheory.V.Ws.H5

section Det

variable {n : ℕ} {A G : Type} [CommRing A] [Group G]

def twA (γ : G →* Aˣ) (B : Type) [CommRing B] [Algebra A B] : MonoidAlgebra B G →ₐ[B] MonoidAlgebra B G :=
  MonoidAlgebra.lift B (MonoidAlgebra B G) G
    { toFun := fun g => MonoidAlgebra.single g (algebraMap A B (γ g))
      map_one' := by simp [← MonoidAlgebra.one_def]
      map_mul' := fun g h => by simp [MonoidAlgebra.single_mul_single] }

theorem twA_single (γ : G →* Aˣ) (B : Type) [CommRing B] [Algebra A B] (g : G) (b : B) :
    twA γ B (MonoidAlgebra.single g b) = MonoidAlgebra.single g (b * algebraMap A B (γ g)) := by
  simp [twA, MonoidAlgebra.lift_single]

def twD (D : GDet n A G) (γ : G →* Aˣ) : GDet n A G where
  D B _ _ := (D.D B).comp (twA γ B).toMonoidHom
  nat B B' _ _ _ _ f x := by
    change D.D B' (twA γ B' _) = f (D.D B (twA γ B x))
    rw [← D.nat]
    congr 1
    induction x using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | single g r => simp [twA_single]
  homog B _ _ b x := by
    change D.D B (twA γ B (b • x)) = b ^ n * D.D B (twA γ B x)
    rw [map_smul, D.homog]

theorem isTwist_twD (D : GDet n A G) (γ : G →* Aˣ) : D.IsTwist γ (twD D γ) := fun _ _ _ _ => rfl

theorem eq_twD {D D' : GDet n A G} {γ : G →* Aˣ} (h : D.IsTwist γ D') : D' = twD D γ :=
  GDet.ext fun B _ _ y => h B y

theorem chi_twD (D : GDet n A G) (γ : G →* Aˣ) (y : MonoidAlgebra A G) : (twD D γ).chi y = D.chi (twA γ A y) := by
  change D.D (Polynomial A) (twA γ (Polynomial A) _) = D.D (Polynomial A) _
  congr 1
  rw [map_sub, twA_single]
  congr 1
  · simp
  · induction y using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | single g r => simp [twA_single]

theorem lam_twD (D : GDet n A G) (γ : G →* Aˣ) (i : ℕ) (y : MonoidAlgebra A G) :
    (twD D γ).lam i y = D.lam i (twA γ A y) := by
  simp only [GDet.lam, chi_twD]

end Det

variable {l : ℕ} [Fact l.Prime]

structure Anti (F : GFrame l) {Q : Type} [CommGroup Q] (γ : F.G₀ →* Q) : Prop where
  conj : ∀ g, γ (F.conj g) * γ g = 1
  iu : ∀ u, F.Iu u ≤ γ.ker
  i0 : F.I0 ≤ γ.ker
  mu : ∀ v (g : F.Gv v), g ∈ F.mu v → γ (F.φ v g) = 1

theorem Anti.mono {F : GFrame l} {Q Q' : Type} [CommGroup Q] [CommGroup Q'] {γ : F.G₀ →* Q} {γ' : F.G₀ →* Q'}
    (h : Anti F γ) (hk : γ.ker ≤ γ'.ker) : Anti F γ' where
  conj g := by
    rw [← map_mul]
    exact hk (show γ _ = 1 by rw [map_mul]; exact h.conj g)
  iu u := (h.iu u).trans hk
  i0 := h.i0.trans hk
  mu v g hg := hk (h.mu v g hg)

structure TwCh (F : GFrame l) {R : Type} [CommRing R] [IsLocalRing R] (γ : F.G₀ →* Rˣ) : Prop extends Anti F γ where
  cont : AdicCont (maximalIdeal R) fun g => (γ g : R)
  red : ∀ g, (γ g : R) - 1 ∈ maximalIdeal R

theorem TwCh.one (F : GFrame l) (R : Type) [CommRing R] [IsLocalRing R] : TwCh F (1 : F.G₀ →* Rˣ) where
  conj g := by simp
  iu u := by simp
  i0 := by simp
  mu v g _ := rfl
  cont N := IsLocallyConstant.of_constant _ fun _ _ => rfl
  red g := by simp

variable {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ} {r : Resid F O n}

def TwMap (B : UniversalOrdinaryDeterminantRing r) {R : Type} [CommRing R] (f₀ f : B.B →+* R) (γ : F.G₀ →* Rˣ) : Prop :=
  (∀ (g : F.G₀) (i : ℕ), i ≤ n → f (B.u.D.lam i (MonoidAlgebra.single g 1)) =
    (γ g : R) ^ i * f₀ (B.u.D.lam i (MonoidAlgebra.single g 1))) ∧
  ∀ v i (g : F.Gv v), f (B.u.ψ v i g) = f₀ (B.u.ψ v i g) * γ (F.φ v g)

theorem TwMap.refl (B : UniversalOrdinaryDeterminantRing r) {R : Type} [CommRing R] (f : B.B →+* R) : TwMap B f f 1 :=
  ⟨fun g i _ => by simp, fun v i g => by simp⟩

theorem TwMap.comp {B : UniversalOrdinaryDeterminantRing r} {R R' : Type} [CommRing R] [CommRing R'] {f₀ f : B.B →+* R} {γ : F.G₀ →* Rˣ}
    (h : TwMap B f₀ f γ) (e : R →+* R') : TwMap B (e.comp f₀) (e.comp f) (pushCh e γ) :=
  ⟨fun g i hi => by simp [h.1 g i hi], fun v i g => by simp [h.2 v i g]⟩

theorem TwMap.trans {B : UniversalOrdinaryDeterminantRing r} {R : Type} [CommRing R] {f₀ f₁ f₂ : B.B →+* R} {γ γ' : F.G₀ →* Rˣ}
    (h : TwMap B f₀ f₁ γ) (h' : TwMap B f₁ f₂ γ') : TwMap B f₀ f₂ (γ * γ') :=
  ⟨fun g i hi => by rw [h'.1 g i hi, h.1 g i hi]; simp [mul_pow]; ring, fun v i g => by rw [h'.2 v i g, h.2 v i g]; simp [mul_assoc]⟩

end UpperTheory.V.Ws.H5

end
