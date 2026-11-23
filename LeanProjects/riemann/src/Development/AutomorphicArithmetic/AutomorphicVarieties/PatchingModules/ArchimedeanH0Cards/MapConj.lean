import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.ObstructionBoundFromDuality
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsTerSide
open Matrix Filter ReciprocityTheory.Gal UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.B2

private theorem map_conj {A X X' : Type} [CommRing A] [CommRing X] [CommRing X'] [Algebra A X] [Algebra A X'] {n : ℕ}
    (u : X →ₗ[A] X') (P Q : Matrix (Fin n) (Fin n) A) (M : Matrix (Fin n) (Fin n) X) :
    (P.map (algebraMap A X) * M * Q.map (algebraMap A X)).map u =
      P.map (algebraMap A X') * M.map u * Q.map (algebraMap A X') := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun k' _ => ?_
  rw [mul_comm _ (algebraMap A X _), mul_comm _ (algebraMap A X' _), ← Algebra.smul_def, ← Algebra.smul_def,
    ← Algebra.smul_def, ← Algebra.smul_def, map_smul, map_smul]

private def odMap {A X X' : Type} [CommRing A] [CommRing X] [CommRing X'] [Algebra A X] [Algebra A X'] (n a : ℕ)
    (u : X →ₗ[A] X') : Od A X n a →ₗ[A] Od A X' n a where
  toFun M := ⟨(M : Matrix (Fin n) (Fin n) X).map u, fun i j => ⟨fun e => by
    have := (M.2 i j).1 e
    rw [Submodule.mem_bot] at this ⊢
    rw [Matrix.map_apply, this, map_zero], fun _ => Submodule.mem_top⟩⟩
  map_add' M N := by ext i j; simp
  map_smul' c M := by ext i j; simp

private theorem lift_ex {A M Q Q' : Type} [CommRing A] [AddCommGroup M] [AddCommGroup Q]
    [AddCommGroup Q'] [Module A M] [Module A Q] [Module A Q'] (π : M →ₗ[A] Q)
    (hπ : Function.Surjective π) (g : M →ₗ[A] Q') (hk : ∀ m, π m = 0 → g m = 0) :
    ∃ q : Q →ₗ[A] Q', ∀ m, q (π m) = g m :=
  _root_.UpperTheory.Reformulated.B.Qf12.lift_ex π hπ g hk

theorem UpperTheory.V.Pa.B2.odHom :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (X : Type) [CommRing X] [Algebra x.A X] (X' : Type) [CommRing X'] [Algebra x.A X'] (D D' : Dat x.A (plOf G)) (o : IsOd h x X D) (o' : IsOd h x X' D') (u : X →ₗ[x.A] X'), ∃ f : D.Hom D', Induced o o' u f := by
  intro l _ L G G0 h n x X _ _ X' _ _ D D' o o' u
  let f : D.M.X →ₗ[x.A] D'.M.X := o'.e.symm.toLinearMap ∘ₗ odMap n x.a u ∘ₗ o.e.toLinearMap
  have hf : ∀ m, (o'.e (f m) : Matrix (Fin n) (Fin n) X') = (o.e m : Matrix (Fin n) (Fin n) X).map u := fun m => by
    simp only [f, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    rfl
  have h0 : ∀ (g : G.G₀) m, f (D.M.ρ g m) = D'.M.ρ g (f m) := fun g m => by
    apply o'.e.injective
    apply Subtype.ext
    rw [hf, o.act, o'.act, hf]
    exact map_conj u _ _ _
  have hc : ∀ m, f (D.M.ρ G.c m) = D'.M.ρ G.c (f m) := fun m => by
    apply o'.e.injective
    apply Subtype.ext
    rw [hf, o.actc, o'.actc, hf]
    ext i j
    simp
  have hall : ∀ (g : G.Γ) m, f (D.M.ρ g m) = D'.M.ρ g (f m) := fun g m => by
    rcases Int.units_eq_one_or (G.η g) with e | e
    · exact h0 ⟨g, e⟩ m
    · have hm : g * G.c ∈ G.η.ker := by
        rw [MonoidHom.mem_ker, map_mul, e, G.η_c]; simp
      have eg : g * G.c * G.c = g := by rw [mul_assoc, G.c_sq, mul_one]
      have e1 := h0 ⟨g * G.c, hm⟩ (D.M.ρ G.c m)
      rw [hc, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul] at e1
      simpa only [eg] using e1
  have hk : ∀ w m, D.π w m = 0 → (D'.π w ∘ₗ f) m = 0 := by
    rintro (v | w) m hm
    · rw [LinearMap.comp_apply, o'.kerV]
      intro i j hij
      have e := congrFun (congrFun (map_conj u (((x.w v)⁻¹ : GL (Fin n) x.A) : Matrix (Fin n) (Fin n) x.A)
        (x.w v : Matrix (Fin n) (Fin n) x.A) (o.e m : Matrix (Fin n) (Fin n) X)) i) j
      rw [hf]
      refine e.symm.trans ?_
      have := (o.kerV v m).1 hm i j hij
      rw [Matrix.map_apply]
      exact (congrArg u this).trans (map_zero u)
    · have : m = 0 := o.kerU w (hm.trans (map_zero _).symm)
      rw [this, map_zero]
  choose q hq using fun w => lift_ex (D.π w) (D.surj w) (D'.π w ∘ₗ f) (hk w)
  exact ⟨⟨f, q, hall, hq⟩, hf⟩
