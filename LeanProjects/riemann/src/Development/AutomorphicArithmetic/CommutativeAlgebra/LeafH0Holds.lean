import Mathlib
import Development.EtaleCohomology.EtaleSheaves.H0TwistOverClosedField
import Development.AutomorphicArithmetic.CommutativeAlgebra.TwistedSectionEqNsmulGeneratorOfConnected

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4

private theorem tw_q_nsmul {q : ℕ} {i : ℤ} {U : Scheme.{0}} (a : Sec (tw q i) U) : q • a = 0 := by
  have h : ((q : ℕ) : ULift.{1} (ZMod q)) = 0 := by
    apply ULift.ext
    simp
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q)), h, zero_smul]

private theorem tw_nsmul_mod {q : ℕ} {i : ℤ} {U : Scheme.{0}} (a : Sec (tw q i) U) (n : ℕ) :
    n • a = (n % q) • a := by
  conv_lhs => rw [← Nat.mod_add_div n q]
  rw [add_smul, mul_smul, tw_q_nsmul, add_zero]

private theorem mod_eq_of_nsmul_eq {q : ℕ} [NeZero q] {i : ℤ} {U : Scheme.{0}} [Nonempty U]
    (ζ : Prim q Γ(U, ⊤)) {c c' : ℕ} (h : c • twGen i ζ = c' • twGen i ζ) : c % q = c' % q := by
  have key : ∀ {c c' : ℕ}, c ≤ c' → c • twGen i ζ = c' • twGen i ζ → c % q = c' % q := by
    intro c c' hle h
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
    rw [add_nsmul] at h
    have h0 : d • twGen i ζ = 0 := by
      have h' := h.symm
      rwa [add_eq_left] at h'
    obtain ⟨k, rfl⟩ := (GlobalTheory.T.tateTwist_sections_locally_generated q i).2.2.1 U ζ d h0
    rw [Nat.add_mul_mod_self_left]
  rcases le_total c c' with hle | hle
  · exact key hle h
  · exact (key hle h.symm).symm

private theorem res_nsmul {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (k : V ⟶ U) (n : ℕ)
    (a : Sec F U) : Sec.res k (n • a) = n • Sec.res k a :=
  map_nsmul (F.obj.map k.op).hom n a

private theorem exists_prim (q : ℕ) [NeZero q] (Ω : Type) [Field Ω] [IsAlgClosed Ω] (hq : IsUnit (q : Ω)) :
    Nonempty (Prim q Ω) := by
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic q Ω)
    (Polynomial.degree_cyclotomic_pos q Ω (Nat.pos_of_ne_zero (NeZero.ne q))).ne'
  refine ⟨⟨ζ, hq, ?_⟩⟩
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
  exact hζ

theorem UpperTheory.leafH0_holds :
    LateralTheory.E.E4.H0TwistOverClosedField := by
  intro hyp q _ Ω _ _ hq i
  obtain ⟨-, e, he, -⟩ := hyp.2.2.2.2.2.2.2.1 (ZMod q) (tw q i)
  obtain ⟨ζ0⟩ := exists_prim q Ω hq
  let ζ : Prim q Γ(Sp Ω, ⊤) :=
    Prim.map (CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv) ζ0
  have hsec : ∀ {X : Scheme.{0}} [ConnectedSpace X] (ξ : Prim q Γ(X, ⊤)) (y : Sec (tw q i) X),
      ∃ c < q, y = c • twGen i ξ := by
    intro X _ ξ y
    obtain ⟨c, rfl⟩ := UpperTheory.twisted_section_eq_nsmul_generator_of_connected q i X ξ y
    exact ⟨c % q, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne q)), tw_nsmul_mod _ c⟩
  refine ⟨?_, ?_⟩
  · have hsurj : Function.Surjective (fun k : Fin q => e (Sp Ω) ((k : ℕ) • twGen i ζ)) := by
      intro x
      obtain ⟨c, hc, hy⟩ := hsec ζ ((e (Sp Ω)).symm x)
      refine ⟨⟨c, hc⟩, ?_⟩
      show e (Sp Ω) (c • twGen i ζ) = x
      rw [← hy, AddEquiv.apply_symm_apply]
    exact Finite.of_surjective _ hsurj
  · intro X _ c
    have hcomm : ∀ s, pl q i c 0 (e (Sp Ω) s) = e X (Sec.res c s) := fun s => he c s
    have hres : Function.Bijective (Sec.res (F := tw q i) c) := by
      have ht : Sec.res c (twGen i ζ) =
          twGen i (Prim.map (CommRingCat.Hom.hom (Scheme.Hom.appTop c)) ζ) :=
        (GlobalTheory.T.tateTwist_sections_locally_generated q i).2.2.2.1 X (Sp Ω) c ζ
      constructor
      · intro s s' hss
        obtain ⟨c1, -, rfl⟩ := hsec ζ s
        obtain ⟨c2, -, rfl⟩ := hsec ζ s'
        rw [res_nsmul, res_nsmul, ht] at hss
        have hm := mod_eq_of_nsmul_eq _ hss
        rw [tw_nsmul_mod _ c1, tw_nsmul_mod _ c2, hm]
      · intro y
        obtain ⟨c1, -, rfl⟩ := hsec (Prim.map (CommRingCat.Hom.hom (Scheme.Hom.appTop c)) ζ) y
        exact ⟨c1 • twGen i ζ, by rw [res_nsmul, ht]⟩
    have hfun : (pl q i c 0 : _ → _) = (e X) ∘ Sec.res c ∘ (e (Sp Ω)).symm := by
      funext x
      simp only [Function.comp]
      rw [← hcomm, AddEquiv.apply_symm_apply]
    rw [hfun]
    exact (e X).bijective.comp (hres.comp (e (Sp Ω)).symm.bijective)
