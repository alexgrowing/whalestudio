import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.WorkKilledC

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global

namespace PositivityTheory.Lit1.GEN.QuotientActionGlobalEulerCharacteristic

local notation "ℚ̄" => AlgebraicClosure ℚ

open W_killed_c

def addAct {G : Type} [Group G] (M : Rep.{0} (ULift.{0} ℤ) G) : G →* AddMonoid.End M where
  toFun g := (M.ρ g).toAddMonoidHom
  map_one' := by ext x; simp <;> rfl
  map_mul' g h := by ext x; simp <;> rfl

def zmodRep (n : ℕ) {G V : Type} [Group G] [AddCommGroup V] [Module (ZMod n) V] (φ : G →* AddMonoid.End V) :
    Representation (ZMod n) G V where
  toFun g := (φ g).toZModLinearMap n
  map_one' := by ext x; simp <;> rfl
  map_mul' g h := by ext x; simp only [map_mul]; rfl

theorem nonempty_iso_of_addEquiv {k G : Type} [CommRing k] [Group G] (hk : Function.Surjective (Int.cast : ℤ → k))
    (A B : Rep.{0} k G) (e : A ≃+ B) (h : ∀ (g : G) (x : A), e (A.ρ g x) = B.ρ g (e x)) : Nonempty (A ≅ B) := by
  let f : A ≃ₗ[k] B :=
    { e with
      map_smul' := fun c x => by
        obtain ⟨n, rfl⟩ := hk c
        show e ((n : k) • x) = (n : k) • e x
        rw [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul, map_zsmul] }
  exact ⟨Rep.mkIso (Representation.Equiv.mk f fun g => LinearMap.ext fun x => h g x)⟩

set_option maxHeartbeats 800000 in
theorem quotient_representation_open (ℓ : ℕ) [Fact ℓ.Prime] (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1)))
    (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
    (L : FiniteSubfield) [Fact (K ≤ L)]
    (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
    [hN : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).Normal]
    (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Module (ZMod ℓ) M]
    (htriv : ∀ g ∈ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)), M.ρ g = 1) :
    ∃ (ρ : Representation (ZMod ℓ) (galUnramifiedOutside K.1 ℚ̄ S ⧸ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) M),
      (∀ (g : galUnramifiedOutside K.1 ℚ̄ S) (m : M), ρ (QuotientGroup.mk g) m = M.ρ g m) ∧
      gsEulerRatio S M ιr = (haveI := isDiscreteRep_infl (gsOpenSubgroup S hL) ρ; gsEulerRatio S (infl (gsOpenSubgroup S hL) ρ) ιr) := by
  have hker : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ≤ (zmodRep ℓ (addAct M)).ker := fun g hg => by
    rw [MonoidHom.mem_ker]
    ext x
    change (M.ρ g) x = x
    rw [htriv g hg]
    rfl
  let ρ : Representation (ZMod ℓ) (galUnramifiedOutside K.1 ℚ̄ S ⧸ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) M :=
    QuotientGroup.lift _ (zmodRep ℓ (addAct M)) hker
  refine ⟨ρ, fun g m => rfl, ?_⟩
  haveI := isDiscreteRep_infl (gsOpenSubgroup S hL) ρ
  obtain ⟨e⟩ := nonempty_iso_of_addEquiv (k := ULift.{0} ℤ) (fun c => ⟨c.down, rfl⟩) M (infl (gsOpenSubgroup S hL) ρ)
    (AddEquiv.refl M) (fun _ _ => rfl)
  exact gsEulerRatio_eq_of_iso S M ιr e

theorem quot_rep (ℓ : ℕ) [Fact ℓ.Prime] (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1)))
    (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
    (L : FiniteSubfield) [Fact (K ≤ L)]
    (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
    [hN : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).Normal]
    (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M]
    (hℓ : ∀ m : M, ℓ • m = 0) (htriv : ∀ g ∈ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)), M.ρ g = 1) :
    ∃ (_ : Module (ZMod ℓ) M) (ρ : Representation (ZMod ℓ) (galUnramifiedOutside K.1 ℚ̄ S ⧸ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) M),
      (∀ (g : galUnramifiedOutside K.1 ℚ̄ S) (m : M), ρ (QuotientGroup.mk g) m = M.ρ g m) ∧
      gsEulerRatio S M ιr = (haveI := isDiscreteRep_infl (gsOpenSubgroup S hL) ρ; gsEulerRatio S (infl (gsOpenSubgroup S hL) ρ) ιr) := by
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  letI inst : Module (ZMod ℓ) M := AddCommGroup.zmodModule hℓ
  exact ⟨inst, quotient_representation_open ℓ K S ιr L hL M htriv⟩

end PositivityTheory.Lit1.GEN.QuotientActionGlobalEulerCharacteristic
