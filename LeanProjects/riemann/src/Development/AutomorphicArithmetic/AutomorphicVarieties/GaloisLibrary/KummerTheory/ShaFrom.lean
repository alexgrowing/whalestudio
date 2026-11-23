import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ClPullApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.PullOnto
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.PlaceDict

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum
open Pointwise

private theorem two_inj {l : ℕ} [Fact l.Prime] (hl : l ≠ 2) (r : ℕ) (m : ZMod (l ^ r)) (h : 2 • m = 0) : m = 0 := by
  have hc : Nat.Coprime 2 (l ^ r) :=
    Nat.Coprime.pow_right r ((Nat.coprime_primes Nat.prime_two Fact.out).2 hl.symm)
  have hu : IsUnit ((2 : ℕ) : ZMod (l ^ r)) := (ZMod.isUnit_iff_coprime 2 _).2 hc
  rw [nsmul_eq_mul] at h
  exact (hu.mul_right_eq_zero).1 h

private theorem hom_one {Γ M : Type} [Group Γ] [AddCommGroup M] {f : Γ → M} (hf : ∀ a b, f (a * b) = f a + f b) :
    f 1 = 0 := by
  have := hf 1 1
  rw [one_mul] at this
  exact left_eq_add.1 this

private theorem hom_conj {Γ M : Type} [Group Γ] [AddCommGroup M] {f : Γ → M} (hf : ∀ a b, f (a * b) = f a + f b)
    (g a : Γ) : f (g * a * g⁻¹) = f a := by
  have h := hf (g * a * g⁻¹) g
  rw [inv_mul_cancel_right, hf, add_comm] at h
  exact (add_right_cancel h).symm

section

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]

private theorem zm_triv (D : LData F Ω l) (r : ℕ) (g) (m : ZMod (l ^ r)) : zmTw D r 0 g m = m := by simp [zmTw]

private theorem mem_iff (D : LData F Ω l) (r : ℕ) (z : Z1 (zmTw D r 0)) :
    (Submodule.Quotient.mk z : H1 (zmTw D r 0)) ∈ ShaZm D r 0 ↔
      ∀ v : D.S, ∀ g ∈ Dec (F := F) (D.A v), z.1 (toGS Ω _ g) = 0 := by
  refine (Submodule.mem_iInf _).trans (forall_congr' fun v => ?_)
  refine ((Submodule.Quotient.mk_eq_zero _).trans (mem_coboundaries1 _ _)).trans ⟨fun ⟨m, hm⟩ g hg => ?_, fun h => ⟨0, fun g => ?_⟩⟩
  · exact (hm ⟨g, hg⟩).trans (sub_eq_zero.2 (zm_triv D r _ m))
  · exact (h g.1 g.2).trans (sub_eq_zero.2 (zm_triv D r _ 0)).symm

private theorem sha_to (D : LData F Ω l) (r : ℕ) (z : Z1 (zmTw D r 0))
    (hx : (Submodule.Quotient.mk z : H1 (zmTw D r 0)) ∈ ShaZm D r 0) :
    (fun u : (⊤ : Subgroup (G F Ω)) => z.1 (toGS Ω _ u.1)) ∈ XDual l ⊤ (ZMod (l ^ r)) (ZMod (l ^ r)) := by
  obtain ⟨p1, p2, p3, p4⟩ := placeDict F Ω
  have hz : ∀ a b, z.1 (a * b) = z.1 a + z.1 b := fun a b => by rw [z.2.2, zm_triv]
  have hdec : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∀ u : (⊤ : Subgroup (G F Ω)), u.1 ∈ Dec (F := F) A →
      z.1 (toGS Ω _ u.1) = 0 := by
    intro A hA u hu
    obtain ⟨v, hv⟩ := p2 A (p3 A l (Fact.out : l.Prime).ne_zero hA)
    have hvS : v ∈ D.S := by
      have := (p4 A v l hv).1 hA
      rw [← D.hS] at this
      exact this
    obtain ⟨g, rfl⟩ := exists_smul_eq_of_isPlaceOver (F := F) (D.hA ⟨v, hvS⟩) hv
    have hc : g⁻¹ * u.1 * g ∈ Dec (F := F) (D.A ⟨v, hvS⟩) := by
      have h : u.1 • g • D.A ⟨v, hvS⟩ = g • D.A ⟨v, hvS⟩ := hu
      show (g⁻¹ * u.1 * g) • D.A ⟨v, hvS⟩ = D.A ⟨v, hvS⟩
      rw [mul_smul, mul_smul, h, inv_smul_smul]
    have h2 := (mem_iff D r z).1 hx ⟨v, hvS⟩ _ hc
    have h3 := hom_conj hz (toGS Ω _ g) (toGS Ω _ (g⁻¹ * u.1 * g))
    rw [h2, ← map_inv, ← map_mul, ← map_mul] at h3
    rw [← h3]
    congr 2
    group
  refine ⟨?_, fun a b => ?_, fun A u hu => ?_, hdec⟩
  · exact (IsLocallyConstant.iff_continuous _).2
      (z.2.1.comp ((continuous_toGS Ω _).comp continuous_subtype_val))
  · show z.1 (toGS Ω _ (a.1 * b.1)) = _
    rw [map_mul, hz]
  · show z.1 (toGS Ω _ u.1) = 0
    by_cases hA : A = ⊤
    · subst hA
      rw [p1, Subgroup.mem_bot] at hu
      rw [hu, map_one, hom_one hz]
    obtain ⟨v, hv⟩ := p2 A hA
    by_cases hl : A.valuation (l : Ω) < 1
    · exact hdec A hl u (Ine_le_Dec A hu)
    have hvS : v ∉ (D.S : Set (HeightOneSpectrum (𝓞 F))) := by
      rw [D.hS]
      exact fun h => hl ((p4 A v l hv).2 h)
    have hn : u.1 ∈ NS Ω (D.S : Set (HeightOneSpectrum (𝓞 F))) := by
      apply Subgroup.le_topologicalClosure
      apply Subgroup.subset_normalClosure
      simp only [Set.mem_iUnion]
      exact ⟨v, hvS, A, hv, hu⟩
    have : toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 F))) u.1 = 1 := (QuotientGroup.eq_one_iff _).2 hn
    rw [this, hom_one hz]

private theorem sha_from (D : LData F Ω l) (r : ℕ) (f : G F Ω → ZMod (l ^ r))
    (hf : (fun u : (⊤ : Subgroup (G F Ω)) => f u.1) ∈ XDual l ⊤ (ZMod (l ^ r)) (ZMod (l ^ r))) :
    f ∈ (ShaZm D r 0).map (resZm D r) := by
  obtain ⟨p1, p2, p3, p4⟩ := placeDict F Ω
  obtain ⟨h1, h2, h3, h4⟩ := hf
  have hc : Continuous f :=
    h1.continuous.comp (continuous_id.subtype_mk fun g : G F Ω => Subgroup.mem_top g)
  have hm : ∀ a b, f (a * b) = f a + f b := fun a b => h2 ⟨a, trivial⟩ ⟨b, trivial⟩
  let N : Subgroup (G F Ω) :=
    { carrier := {n | f n = 0}
      one_mem' := hom_one hm
      mul_mem' := fun {a b} ha hb => by
        show f (a * b) = 0
        rw [hm, ha, hb, add_zero]
      inv_mem' := fun {a} ha => by
        have := hm a⁻¹ a
        rw [inv_mul_cancel, hom_one hm, ha, add_zero] at this
        exact this.symm }
  haveI hN : N.Normal := ⟨fun a ha g => (hom_conj hm g a).trans ha⟩
  have hcl : IsClosed (N : Set (G F Ω)) := isClosed_singleton.preimage hc
  have hv : ∀ n ∈ NS Ω (D.S : Set (HeightOneSpectrum (𝓞 F))), f n = 0 := by
    intro n hn
    refine Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal ?_) hcl hn
    intro τ hτ
    simp only [Set.mem_iUnion] at hτ
    obtain ⟨v, -, A', -, hτ⟩ := hτ
    exact h3 A' ⟨τ, trivial⟩ hτ
  let f' : GS Ω (D.S : Set (HeightOneSpectrum (𝓞 F))) → ZMod (l ^ r) := Quotient.lift f fun a b hab => by
    have e1 := hv _ (QuotientGroup.leftRel_apply.1 hab)
    have e2 := hm a (a⁻¹ * b)
    rw [mul_inv_cancel_left, e1, add_zero] at e2
    exact e2.symm
  refine ⟨Submodule.Quotient.mk ⟨f', hc.quotient_lift _, fun a b => ?_⟩, (mem_iff D r _).2 fun v g hg => ?_, rfl⟩
  · obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    rw [zm_triv]
    exact hm a b
  · refine h4 (D.A v) ((p4 _ v.1 l (D.hA v)).2 ?_) ⟨g, trivial⟩ hg
    rw [← D.hS]
    exact v.2

end

theorem UpperTheory.V.Kum.shaZm :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (D : LData F Ω l) (r : ℕ), PTCase F l → Function.Injective (resZm D r) ∧
    (ShaZm D r 0).map (resZm D r) = (ClDual F l (ZMod (l ^ r)) (ZMod (l ^ r))).map (LinearMap.funLeft (ZMod (l ^ r)) (ZMod (l ^ r)) (artCl F Ω)) := by
  intro F Ω _ _ _ _ _ l _ D r hP
  have hU : (⊤ : Subgroup (G F Ω)) ≤ galOf F F Ω := (galOf_self F Ω).ge
  have key := pullOnto F Ω F ⊤ hU l (ZMod (l ^ r)) (ZMod (l ^ r)) (Fact.out : l.Prime).ne_zero le_top
    (hP.elim (fun h => Or.inr (two_inj h r)) fun h => Or.inl (nrRealPlaces_eq_zero_iff.1 h))
  refine ⟨fun x y hxy => ?_, le_antisymm ?_ ?_⟩
  · obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨z', rfl⟩ := Submodule.Quotient.mk_surjective _ y
    have e : z = z' := Subtype.ext (funext fun g => by
      obtain ⟨σ, rfl⟩ : ∃ σ, toGS Ω _ σ = g := QuotientGroup.mk_surjective g
      exact congrFun hxy σ)
    rw [e]
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have h := sha_to D r z hx
    rw [← key] at h
    obtain ⟨θ, hθ, e⟩ := h
    exact ⟨θ, hθ, funext fun g => congrFun e ⟨g, trivial⟩⟩
  · rintro _ ⟨θ, hθ, rfl⟩
    refine sha_from D r _ ?_
    rw [← key]
    exact ⟨θ, hθ, rfl⟩
