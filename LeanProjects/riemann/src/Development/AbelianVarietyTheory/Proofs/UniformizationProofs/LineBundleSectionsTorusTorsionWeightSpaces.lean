import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ClassSubStructure
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsConj
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CardTorsionOverZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.DimEqAddFinrankOfKernel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpFLinear
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorusTorsionToAbelianTorsionThetaActionStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFourierJacobiExpansionOverFieldStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FourierJacobiExpansionOverFieldInjectiveStatement

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section

namespace GlobalTheory.UU.Weight

open GlobalTheory.TorusExt GlobalTheory.ClassWeight

abbrev SecA {R : Type} [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (k : ℕ) : Type :=
  SecMod (F := F) (fst (TFK (R := R) F) A.A).left (LPow A.A A.L (k : ℤ) (TFK (R := R) F))

theorem exists_expansion (hL : Laws) (hL₂ : Laws2) : AllPre fun {V} _ _ _ {D} {A} {_} _ _ U =>
    ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k →
      ∃ S : ∀ α, SecA A F k →ₗ[F] CompMod D F k α,
        (∀ (v : SecA A F k) (s : Raw D F k), U.ExpF F k v.sec s ↔ s = fun α => (S α v).sec) ∧
        ∀ v, (∀ α, S α v = 0) → v = 0 := by
  intro V _ _ _ hV D A G _ _ U F _ _ k hk
  choose x hx using GlobalTheory.T.exists_fourierJacobi_expansion_over_field hL hL₂ V hV D A G U F k hk
  have uq := GlobalTheory.T.fourierJacobiExpansion_overField_injective V hV D A G U F k
  have lin := ExpLin.expF_linear V hV D A G U F k
  let S₀ : ∀ α, SecA A F k → CompMod D F k α := fun α v => SecMod.mk _ (x v.sec α)
  have comb : ∀ (c : F) (v v' : SecA A F k) α, S₀ α (c • v + v') = c • S₀ α v + S₀ α v' := fun c v v' =>
    congrFun ((uq _ _ _ _ (hx (c • v + v').sec) (lin v.sec v'.sec (c • v + v').sec _ _
      (fun α => (c • S₀ α v + S₀ α v').sec) c (hx v.sec) (hx v'.sec) (fun _ => rfl) fun _ _ => rfl)).1 rfl)
  have z : ∀ α, S₀ α 0 = 0 := fun α => by
    have := comb 1 0 0 α
    rw [one_smul, one_smul, add_zero] at this
    exact left_eq_add.1 this
  refine ⟨fun α =>
    { toFun := S₀ α
      map_add' := fun v v' => by simpa only [one_smul] using comb 1 v v' α
      map_smul' := fun c v => by simpa only [add_zero, z, RingHom.id_apply] using comb c v 0 α },
    fun v s => ⟨fun h => (uq _ _ _ _ h (hx v.sec)).1 rfl, fun h => h ▸ hx v.sec⟩, fun v h => ?_⟩
  exact (uq _ _ _ _ (hx v.sec) (hx (0 : SecA A F k).sec)).2 (funext fun α => (h α).trans (z α).symm)

theorem exists_rep (hL : Laws) (hL₂ : Laws2) {R : Type} [CommRing R] [IsDomain R]
    (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [IsAlgClosed F]
    [Algebra (FractionRing R) F] {N : ℕ} (hN : (N : F) ≠ 0) :
    ∃ (Φ : TorsPt A (TFK (R := R) F) N → (SecA A F N ≃ₗ[F] SecA A F N))
      (e : TorsPt A (TFK (R := R) F) N → TorsPt A (TFK (R := R) F) N → Fˣ),
      Module.finrank F (SecA A F N) = N ^ A.g ∧ Nat.card (TorsPt A (TFK (R := R) F) N) = N ^ (2 * A.g) ∧
      (∀ a, ∃ θ : ThetaGrp A.A A.L N (TFK (R := R) F), θ.pt = a.1 ∧ ∀ v, IsActOf A.A A.L N θ v.sec (Φ a v).sec) ∧
      (∀ a b, ∃ c : Fˣ, ∀ v, Φ (a * b) v = (c : F) • Φ a (Φ b v)) ∧
      (∀ a b v, Φ a (Φ b v) = (e a b : F) • Φ b (Φ a v)) ∧ ∀ a, (∀ b, e a b = 1) → a = 1 := by
  obtain ⟨Φ, e, hd, h⟩ := exists_projective_rep hL hL₂ A (jFK (R := R) F) hN
  exact ⟨Φ, e, hd, (hL.mulN _ A N (Nat.pos_of_ne_zero fun e => hN (by rw [e, Nat.cast_zero]))).2.2.2.2 F
    (jFK (R := R) F) hN, h⟩

attribute [local instance] gtGroup

theorem exists_range {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (N : ℕ) {A : Type} [CommGroup A] (m : {g : GtPtF D F // GtTors D N g} → A)
    (minj : Function.Injective m) (madd : ∀ g g' g'', GtPtF.IsAdd g.1 g'.1 g''.1 → m g'' = m g * m g') :
    ∃ (H : Subgroup A) (a : TorChar D.X F N →* A), (∀ h, h ∈ H ↔ ∃ g, m g = h) ∧
      Nat.card H = Nat.card {g : GtPtF D F // GtTors D N g} ∧ Function.Injective a ∧
      ∀ τ, ∃ g, a τ = m g ∧ g.1 = torusPt D F (Additive.ofMul τ.1) := by
  let K := (nsmulAddMonoidHom N : GtPtF D F →+ GtPtF D F).ker
  let κ : K ≃ {g : GtPtF D F // GtTors D N g} := Equiv.subtypeEquivRight fun g => (GtCount.gtTors_iff N g).symm
  let ν : Multiplicative K →* A :=
    MonoidHom.mk' (fun g => m (κ g.toAdd)) fun g g' => madd _ _ _ ((isAdd_iff_eq _ _ _).2 rfl)
  have hν : Function.Injective ν := fun g g' h => κ.injective (minj h)
  let i : TorChar D.X F N →* Multiplicative K := MonoidHom.mk' (fun τ => Multiplicative.ofAdd
    ⟨torusPt D F (Additive.ofMul τ.1), show N • torusPt D F (Additive.ofMul τ.1) = 0 by
      rw [← map_nsmul, ← ofMul_pow, show τ.1 ^ N = 1 from τ.2, ofMul_one, map_zero]⟩)
    fun τ τ' => Subtype.ext (map_add (torusPt D F) (Additive.ofMul τ.1) (Additive.ofMul τ'.1))
  have iinj : Function.Injective i := fun τ τ' h =>
    Subtype.ext (Additive.ofMul.injective (torusPt_injective (congrArg Subtype.val h)))
  exact ⟨ν.range, ν.comp i, fun h => ⟨fun ⟨g, e⟩ => ⟨_, e⟩, fun ⟨g, e⟩ =>
      ⟨Multiplicative.ofAdd (κ.symm g), (congrArg m (κ.apply_symm_apply g)).trans e⟩⟩,
    (Nat.card_congr (MonoidHom.ofInjective hν).toEquiv).symm.trans (Nat.card_congr κ), hν.comp iinj,
    fun τ => ⟨κ (i τ).toAdd, rfl, rfl⟩⟩

theorem structure_of_acts (hL : Laws) (hL₂ : Laws2) {V : Type} [CommRing V] [IsDomain V] [IsNoetherianRing V] {I : Ideal V}
    {D : DegPre V} {A : PolAV (Spec (CommRingCat.of (FractionRing V)))} {G : Over (Spec (CommRingCat.of V))} [GrpObj G]
    [IsCommMonObj G] (U : PreU I D A G) (hg : A.g = D.P.g + D.rank) (F : Type) [Field F] [IsAlgClosed F]
    [Algebra (FractionRing V) F] {N : ℕ} (hN : (N : F) ≠ 0) (S : ∀ α, SecA A F N →ₗ[F] CompMod D F N α)
    (hS : ∀ (v : SecA A F N) (s : Raw D F N), U.ExpF F N v.sec s ↔ s = fun α => (S α v).sec)
    (hS₀ : ∀ v, (∀ α, S α v = 0) → v = 0)
    (m : {g : GtPtF D F // GtTors D N g} → (TFK (R := V) F ⟶ A.A)) (minj : Function.Injective m)
    (mact : ∀ g, U.Acts F N 0 g.1 (m g)) (madd : ∀ g g' g'', GtPtF.IsAdd g.1 g'.1 g''.1 → m g'' = m g * m g') :
    ∃ Ψ : {g : GtPtF D F // GtTors D N g} → (SecA A F N ≃ₗ[F] SecA A F N), FiniteDimensional F (SecA A F N) ∧
      (∀ g : {g : GtPtF D F // GtTors D N g}, ∃ w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F g.1.b) (DegPre.lineε N)), w.IsGen ∧
        ∀ v : SecA A F N, PhiRaw D F N 0 g.1 w (fun α => (S α v).sec) fun α => (S α (Ψ g v)).sec) ∧
      ∀ α, (∀ v, ∃ v' ∈ classSub S N α, ∀ mu, S (α + N • mu) v' = S (α + N • mu) v) ∧
        Module.finrank F (classSub S N α) = N ^ D.P.g ∧
        ∀ W : Submodule F (SecA A F N), W ≤ classSub S N α → (∀ g, ∀ v ∈ W, Ψ g v ∈ W) →
          W = ⊥ ∨ W = classSub S N α := by
  have hN0 : N ≠ 0 := fun e => hN (by rw [e, Nat.cast_zero])
  have hN1 : 0 < N := Nat.pos_of_ne_zero hN0
  obtain ⟨Φ, e, hd, cA, hθ, hm, hc, hn⟩ := exists_rep hL hL₂ A F hN
  have : Finite (TorsPt A (TFK (R := V) F) N) :=
    Nat.finite_of_card_ne_zero (cA.trans_ne (pow_ne_zero _ hN0))
  have fd : FiniteDimensional F (SecA A F N) :=
    Module.finite_of_finrank_pos ((pow_pos hN1 _).trans_eq hd.symm)
  obtain ⟨m', hm'⟩ : ∃ m' : {g : GtPtF D F // GtTors D N g} → TorsPt A (TFK (R := V) F) N,
    ∀ g, (m' g).1 = m g := ⟨fun g => ⟨m g, (mact g).1⟩, fun _ => rfl⟩
  have hΨ : ∀ g : {g : GtPtF D F // GtTors D N g}, ∃ w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F g.1.b) (DegPre.lineε N)), w.IsGen ∧
      ∀ v : SecA A F N, PhiRaw D F N 0 g.1 w (fun α => (S α v).sec) fun α => (S α (Φ (m' g) v)).sec := fun g => by
    obtain ⟨θ, h₁, h₂⟩ := hθ (m' g)
    obtain ⟨w, hw, h⟩ := (mact g).2 θ (h₁.trans (hm' g))
    exact ⟨w, hw, fun v => h _ _ _ _ ((hS v _).2 rfl) ((hS _ _).2 rfl) (h₂ v)⟩
  obtain ⟨H, a, hH, cH, ainj, ha⟩ := exists_range D F N m'
    (fun g g' h => minj ((hm' g).symm.trans ((congrArg Subtype.val h).trans (hm' g'))))
    fun g g' g'' h => Subtype.ext ((hm' g'').trans ((madd g g' g'' h).trans
      (congrArg₂ (· * ·) (hm' g) (hm' g')).symm))
  have cT : Nat.card (TorChar D.X F N) = N ^ D.rank := GtCount.card_torus_torsion D.X F N hN
  rw [(GtCount.card_gtTors hL hL₂ V D F N hN).1] at cH
  have k₁ : ∀ τ, ∃ c : Fˣ, ∀ v α, S α (Φ (a τ) v) = ((c * evalChar F N α τ : Fˣ) : F) • S α v :=
    fun τ => by
      obtain ⟨g, e₁, e₂⟩ := ha τ
      obtain ⟨w, hw, h⟩ := hΨ g
      obtain ⟨c, hc⟩ := phiRaw_torus hL.globalFns τ.1 e₂ g.2 hw
      rw [e₁]
      exact ⟨c, fun v => hc (fun α => S α v) (fun α => S α (Φ (m' g) v)) (h v)⟩
  have k₂ : ∀ h ∈ H, ∀ α v v' (c : F), S α v = c • S α v' → S α (Φ h v) = c • S α (Φ h v') := by
    intro x hx β v v' c e
    obtain ⟨g, rfl⟩ := (hH x).1 hx
    obtain ⟨w, hw, h⟩ := hΨ g
    exact phiRaw_smul hL.globalFns g.2 hw (s := fun α => S α v) (s' := fun α => S α (Φ (m' g) v))
      (t := fun α => S α v') (t' := fun α => S α (Φ (m' g) v')) (h v) (h v') β c e
  refine ⟨fun g => Φ (m' g), fd, hΨ, fun α => ?_⟩
  obtain ⟨h₁, h₂, h₃⟩ := classSub_structure hN e Φ (by rw [cA, Nat.cast_pow]; exact pow_ne_zero _ hN)
    (by rw [cA, hd, mul_comm, pow_mul]) hm hc hn S hS₀ a ainj k₁ H k₂ (by rw [cT, cH, cA, hg]; ring) α
  refine ⟨h₁, ?_, fun W hW hst => h₃ W hW fun x hx => ?_⟩
  · refine Nat.eq_of_mul_eq_mul_right (pow_pos hN1 D.rank) ?_
    rw [← cT, h₂, cT, ← pow_add, ← hg, hd]
  · obtain ⟨g, rfl⟩ := (hH x).1 hx
    exact hst g

theorem weight_structure (hL : Laws) (hL₂ : Laws2) : AllPre fun {V} _ _ _ {D} {A} {_} _ _ U => ∀ N : ℕ, 1 ≤ N →
    ∃ (S : ∀ α, SecA A (Kbar V) N →ₗ[Kbar V] CompMod D (Kbar V) N α)
      (Ψ : {g : GtPtF D (Kbar V) // GtTors D N g} → (SecA A (Kbar V) N ≃ₗ[Kbar V] SecA A (Kbar V) N)),
      FiniteDimensional (Kbar V) (SecA A (Kbar V) N) ∧
      (∀ (v : SecA A (Kbar V) N) (s : Raw D (Kbar V) N), U.ExpF (Kbar V) N v.sec s ↔ s = fun α => (S α v).sec) ∧
      (∀ v, (∀ α, S α v = 0) → v = 0) ∧
      (∀ g : {g : GtPtF D (Kbar V) // GtTors D N g},
        ∃ w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D (Kbar V) g.1.b) (DegPre.lineε N)), w.IsGen ∧
        ∀ v : SecA A (Kbar V) N, PhiRaw D (Kbar V) N 0 g.1 w (fun α => (S α v).sec) fun α => (S α (Ψ g v)).sec) ∧
      ∀ α, (∀ v, ∃ v' ∈ classSub S N α, ∀ mu, S (α + N • mu) v' = S (α + N • mu) v) ∧
        Module.finrank (Kbar V) (classSub S N α) = N ^ D.P.g ∧
        ∀ W : Submodule (Kbar V) (SecA A (Kbar V) N), W ≤ classSub S N α → (∀ g, ∀ v ∈ W, Ψ g v ∈ W) →
          W = ⊥ ∨ W = classSub S N α := by
  intro V _ _ _ hV D A G _ _ U N hN1
  have : IsNoetherianRing V := by have := hV.1; infer_instance
  have hN : (N : Kbar V) ≠ 0 := by
    have := hV.2.2
    have : CharZero (FractionRing V) := inferInstance
    exact Nat.cast_ne_zero.2 (by omega)
  obtain ⟨S, hS, hS₀⟩ := exists_expansion hL hL₂ V hV D A G U (Kbar V) N hN1
  obtain ⟨m, minj, mact, madd⟩ := GlobalTheory.T.torusTorsion_to_abelianTorsion_theta_action hL hL₂ V hV D A G U N hN1
  obtain ⟨Ψ, fd, h⟩ := structure_of_acts hL hL₂ U (PreU.dim_eq V hV D A G U) (Kbar V) hN S hS hS₀ m minj mact madd
  exact ⟨S, Ψ, fd, hS, hS₀, h⟩

theorem main : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {_} _ _ U => ∀ N : ℕ, 1 ≤ N → (∀ (α : D.X) t s, U.ExpF (Kbar V) N t s → ∃ t' s', U.ExpF (Kbar V) N t' s' ∧ ∀ β, (∃ mu, β = α + N • mu) ∧ s' β = s β ∨ (¬ ∃ mu, β = α + N • mu) ∧ ∀ j, (s' β).f j = 0) ∧ (∀ α : D.X, ∃ mu, U.Supp (Kbar V) N (α + N • mu)) ∧ ∀ (α : D.X), U.Supp (Kbar V) N α → ∀ t s, U.ExpF (Kbar V) N t s → (∀ β, (¬ ∃ mu, β = α + N • mu) → ∀ j, (s β).f j = 0) → (∀ j, (s α).f j = 0) → ∀ j, t.f j = 0) := by
  intro hL hL₂ V _ _ _ hV D A G _ _ U N hN
  obtain ⟨S, Ψ, fd, hS, hS₀, hΨ, h⟩ := weight_structure hL hL₂ V hV D A G U N hN
  refine ⟨fun α t s hs => ?_, fun α => ?_, fun α ⟨t₀, s₀, h₀, j₀, hj₀⟩ t s hs hz hα => ?_⟩
  · obtain rfl := (hS (SecMod.mk _ t) s).1 hs
    obtain ⟨v', hv', e⟩ := (h α).1 (SecMod.mk _ t)
    refine ⟨v'.sec, _, (hS v' _).2 rfl, fun β => ?_⟩
    by_cases hβ : ∃ mu, β = α + N • mu
    · refine Or.inl ⟨hβ, ?_⟩
      obtain ⟨mu, rfl⟩ := hβ
      exact e mu
    · exact Or.inr ⟨hβ, (SecMod.eq_zero_iff_coord _).1 (hv' β hβ)⟩
  · have : Nontrivial (classSub S N α) :=
      Module.nontrivial_of_finrank_pos (R := Kbar V) ((pow_pos hN _).trans_eq (h α).2.1.symm)
    obtain ⟨v, hv⟩ := exists_ne (0 : classSub S N α)
    obtain ⟨β, hβ⟩ := not_forall.1 fun e => hv (Subtype.ext (hS₀ v.1 e))
    obtain ⟨mu, rfl⟩ := not_not.1 fun e => hβ (v.2 β e)
    exact ⟨mu, v.1.sec, _, (hS v.1 _).2 rfl, not_forall.1 fun e => hβ ((SecMod.eq_zero_iff_coord _).2 e)⟩
  · obtain rfl := (hS (SecMod.mk _ t) s).1 hs
    obtain rfl := (hS (SecMod.mk _ t₀) s₀).1 h₀
    have st : ∀ g β v, S β v = 0 → S β (Ψ g v) = 0 := fun g β v e => by
      obtain ⟨w, hw, hp⟩ := hΨ g
      exact (phiRaw_smul hL.globalFns g.2 hw (s := fun α => S α v) (s' := fun α => S α (Ψ g v))
        (t := fun α => S α v) (t' := fun α => S α (Ψ g v)) (hp v) (hp v) β 0 (e.trans (zero_smul _ _).symm)).trans (zero_smul _ _)
    rcases (h α).2.2 (classSub S N α ⊓ LinearMap.ker (S α)) inf_le_left
      (fun g v hv => ⟨fun β hβ => st g β v (hv.1 β hβ), st g α v hv.2⟩) with e | e
    · have : SecMod.mk _ t ∈ classSub S N α ⊓ LinearMap.ker (S α) :=
        ⟨fun β hβ => (SecMod.eq_zero_iff_coord _).2 (hz β hβ), (SecMod.eq_zero_iff_coord _).2 hα⟩
      rw [e] at this
      exact (SecMod.eq_zero_iff_coord _).1 ((Submodule.mem_bot _).1 this)
    · obtain ⟨v', hv', e'⟩ := (h α).1 (SecMod.mk _ t₀)
      have e₁ : ∀ β, β = α + N • (0 : D.X) → S β v' = S β (SecMod.mk _ t₀) := fun β hβ => hβ ▸ e' 0
      have e₂ : S α v' = 0 := (e.symm ▸ hv' : v' ∈ classSub S N α ⊓ LinearMap.ker (S α)).2
      exact absurd ((SecMod.eq_zero_iff_coord _).1 ((e₁ α (by rw [nsmul_zero, add_zero])).symm.trans e₂) j₀) hj₀

end GlobalTheory.UU.Weight
