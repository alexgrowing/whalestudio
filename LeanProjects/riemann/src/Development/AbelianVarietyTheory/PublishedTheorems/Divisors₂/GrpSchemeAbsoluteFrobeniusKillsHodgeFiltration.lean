import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ConjugateFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsPerfectOfIsDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheafIffAlt

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published.ConjugateFiltration.Test

variable (p : ℕ) [Fact p.Prime] {R : Type} [CommRing R] (hR : (p : R) = 0)

section Kill

variable {X : Scheme.{0}} {s : X ⟶ Sp R} (T : Thick (dp0 R) s)

include hR in

theorem cast_B : (p : T.B) = 0 := by rw [← map_natCast (algebraMap R T.B), hR, map_zero]

include hR in

theorem cast_B₀ : (p : T.B₀) = 0 := by rw [← map_natCast T.π, cast_B p hR T, map_zero]

def lft : T.B₀ →+* T.B :=
  T.π.liftOfSurjective T.surj ⟨frobR p T.B (cast_B p hR T), fun a ha ↦ by
    have hJ : a ∈ T.J := (T.ker a).1 ha
    rw [RingHom.mem_ker, frobR_apply, ← T.δ.factorial_mul_dpow_eq_pow hJ]
    obtain ⟨c, hc⟩ := Nat.dvd_factorial (Fact.out : p.Prime).pos le_rfl
    rw [hc, Nat.cast_mul, cast_B p hR T, zero_mul, zero_mul]⟩

theorem lft_π (b : T.B) : lft p hR T (T.π b) = b ^ p :=
  (RingHom.liftOfRightInverse_comp_apply _ _ _ _ b).trans (frobR_apply p _ (cast_B p hR T) b)

def red : Thick (dp0 R) s :=
  letI : Algebra R T.B₀ := (T.π.comp (algebraMap R T.B)).toAlgebra
  Thick.triv T.B₀ T.x T.w

variable {hX : (p : Γ(X, ⊤)) = 0}
  (h : IsMor (dp0 R) s (dp0 R) s (frobR p R hR) (GlobalTheory.VB.frob X p hX))

def eta : red T ⟶ h.obj T :=
  letI : Algebra R T.B₀ := (T.π.comp (algebraMap R T.B)).toAlgebra
  Thick.trivHom (hx := T.w) (T := h.obj T)
    { lft p hR T with
      commutes' := fun r ↦ (lft_π p hR T _).trans (by
        change _ = algebraMap R T.B (frobR p R hR r)
        rw [frobR_apply, map_pow]) }
    (by
      have e : T.π.comp (lft p hR T) = frobR p T.B₀ (cast_B₀ p hR T) := RingHom.ext fun b ↦ by
        obtain ⟨b, rfl⟩ := T.surj b
        rw [RingHom.comp_apply, lft_π, frobR_apply, map_pow]
      have h0 : (p : Γ(Sp T.B₀, ⊤)) = 0 := GlobalTheory.SS.FrobField.cast_zero_sp _ (cast_B₀ p hR T)
      change spMap (T.π.comp (lft p hR T)) ≫ T.x = T.x ≫ GlobalTheory.VB.frob X p hX
      rw [e, ← frob_sp p _ _ h0, GlobalTheory.VB.frob_naturality p hX T.x h0])

variable {T} in

def redMap {T' : Thick (dp0 R) s} (φ : T ⟶ T') : red T ⟶ red T' :=
  letI : Algebra R T.B₀ := (T.π.comp (algebraMap R T.B)).toAlgebra
  letI : Algebra R T'.B₀ := (T'.π.comp (algebraMap R T'.B)).toAlgebra
  Thick.trivHom (hx := T.w) (T := Thick.triv T'.B₀ T'.x T'.w)
    { φ.φ₀ with commutes' := fun r ↦ (φ.comm _).trans (congrArg T'.π (φ.φ.commutes r)) } φ.pt

theorem frobenius_kills_hodge_filtration {c : FirstDeRham s} (hc : c ∈ F1 s) : h.pull1 c = 0 := by
  rw [hodgeFiltration_eq_range] at hc
  obtain ⟨f, rfl⟩ := hc
  rw [← h.cl_pullForm]
  refine H1.mk_eq_zero.2 ⟨fun T ↦ ev (T := red T) (T' := h.obj T) f.1 (eta p hR T h), ?_⟩
  funext T T' φ
  have k := Form.ev_sq f (redMap φ) (eta p hR T' h) (eta p hR T h) (h.functor.map φ) rfl rfl fun b ↦ by
    obtain ⟨b, rfl⟩ := T.surj b
    change lft p hR T' (φ.φ₀ (T.π b)) = φ.φ (lft p hR T (T.π b))
    rw [φ.comm, lft_π, lft_π, map_pow]
  exact sub_eq_of_eq_add' k

end Kill

theorem grpScheme_absoluteFrobenius_kills_hodgeFiltration (A : Over (Sp R)) [GrpObj A] (hA : (p : Γ(A.left, ⊤)) = 0)
    (m : GrpMor (dp0 R) (𝟙 _) A (dp0 R) (𝟙 _) A (frobR p R hR) (spMap (frobR p R hR))
      (GlobalTheory.VB.frob A.left p hA)) : ∀ x ∈ PrimitiveSubmodule A, m.pull x = 0 :=
  fun _ hx ↦ Subtype.ext (frobenius_kills_hodge_filtration p hR m.isMor hx)

theorem unit_concl (Φ : primDR (𝟙_ (Over (Sp R))) → primDR (𝟙_ (Over (Sp R)))) :
    (∃ N : Submodule R (primDR (𝟙_ (Over (Sp R)))), IsCompl (Submodule.span R (Set.range Φ)) N) ∧
    (∀ P : PrimeSpectrum R, Module.rankAtStalk (Submodule.span R (Set.range Φ)) P = 0) ∧
    ∀ (B : Over (Sp R)) [GrpObj B] (φ : HdR (𝟙_ (Over (Sp R))) →ₗ[R] HdR B →ₗ[R] R) x y, φ x y = 0 := by
  have : Subsingleton (primDR (𝟙_ (Over (Sp R)))) :=
    ⟨fun a b ↦ (primDR_unit a).trans (primDR_unit b).symm⟩
  refine ⟨⟨⊤, ?_⟩, fun P ↦ congrFun Module.rankAtStalk_eq_zero_of_subsingleton P,
    fun B _ φ x y ↦ by rw [HdR_unit x]; simp⟩
  rw [Subsingleton.elim (Submodule.span R (Set.range Φ)) ⊥]; exact isCompl_bot_top

include hR in

theorem applies (H : ConjugateFiltration) (D : DualAbelianScheme) (F : AbelianDeRham.Free)
    (A : Over (Sp R)) [GrpObj A] (g : ℕ) (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) :
    ∃ (B : Over (Sp R)) (_ : GrpObj B) (P : LB (A ⊗ B).left) (φ : HdR A →ₗ[R] HdR B →ₗ[R] R),
      GlobalTheory.AbDual.IsDual A B P ∧ GlobalTheory.AbDual.IsCorrForm (dp0 R) (𝟙 _) A B P φ ∧
      ∀ x ∈ (conjDR p R hR A).dualAnnihilator, ∀ y ∈ (conjDR p R hR B).dualAnnihilator, φ x y = 0 := by
  obtain ⟨B, _, P, φ, hB, hg', hP, hφ⟩ := PoincareDeRhamDuality.Test.exists_hyp R D F A g hA hg
  refine ⟨B, _, P, φ, hP, hφ, fun x hx y hy ↦ ?_⟩
  exact (H p R hR A g hA hg _ (frobMor p R hR A (cast_left p R hR A))).2.2.2 B hB hg' _
    (frobMor p R hR B (cast_left p R hR B)) P hP φ hφ x y
    (fun c ↦ (Submodule.mem_dualAnnihilator _).1 hx _ (Submodule.subset_span ⟨c, rfl⟩))
    (fun c ↦ (Submodule.mem_dualAnnihilator _).1 hy _ (Submodule.subset_span ⟨c, rfl⟩))

theorem elliptic (H : ConjugateFiltration) (F : AbelianDeRham.Free) (k : Type) [Field k] (hk : (p : k) = 0)
    (W : WeierstrassCurve k) [W.IsElliptic] :
    (∀ P : PrimeSpectrum k, Module.rankAtStalk (conjDR p k hk (GlobalTheory.WeierstrassCurve.ellPolAV W).A) P = 1) ∧
    conjDR p k hk (GlobalTheory.WeierstrassCurve.ellPolAV W).A ≠ ⊥ ∧
    conjDR p k hk (GlobalTheory.WeierstrassCurve.ellPolAV W).A ≠ ⊤ := by
  let E := GlobalTheory.WeierstrassCurve.ellPolAV W
  have hg : SmoothOfRelativeDimension 1 E.A.hom := E.smoothDim
  have h1 : ∀ P : PrimeSpectrum k, Module.rankAtStalk (conjDR p k hk E.A) P = 1 :=
    (H p k hk E.A 1 E.isAb hg _ (frobMor p k hk E.A (cast_left p k hk E.A))).2.2.1
  refine ⟨h1, fun e ↦ ?_, fun e ↦ ?_⟩
  · have := h1 ⊥
    rw [show conjDR p k hk E.A = ⊥ from e, Module.rankAtStalk_eq_zero_of_subsingleton] at this
    simp at this
  · have := h1 ⊥
    rw [Module.rankAtStalk_eq_of_equiv (LinearEquiv.ofTop _ e), (F.prim E.isAb hg).2.2 ⊥] at this
    simp at this

end GlobalTheory.Published.ConjugateFiltration.Test
