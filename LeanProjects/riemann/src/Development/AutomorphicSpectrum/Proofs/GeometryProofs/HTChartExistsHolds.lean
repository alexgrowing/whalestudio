import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HTChartExists
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateFunctionalMulStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeTateLatticeBaseChangePairingStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsHodgeTateFunctionalStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFiniteBaseChangeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateFunctionalEndomorphismStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateFunctionalUniqueStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BT.ChartEx

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField

def powChar {R : Type} [CommRing R] (m : ℕ) [NeZero m] (ζ : Rˣ) (hζ : ζ ^ m = 1) :
    Multiplicative (ZMod m) →* Rˣ where
  toFun k := ζ ^ (Multiplicative.toAdd k).val
  map_one' := by simp
  map_mul' a b := by
    rw [toAdd_mul, ZMod.val_add, ← pow_add]
    exact (pow_eq_pow_mod _ hζ).symm

theorem powChar_apply {R : Type} [CommRing R] (m : ℕ) [NeZero m] (ζ : Rˣ) (hζ : ζ ^ m = 1) (k : ZMod m) :
    powChar m ζ hζ (Multiplicative.ofAdd k) = ζ ^ k.val := rfl

def liftSurj {G T H : Type} [Group G] [Group T] [Group H] (π : G →* T) (hπ : Function.Surjective π)
    (f : G →* H) (hf : ∀ z, π z = 1 → f z = 1) : T →* H :=
  π.liftOfRightInverse (Function.surjInv hπ) (Function.rightInverse_surjInv hπ)
    ⟨f, fun z hz => (MonoidHom.mem_ker).2 (hf z ((MonoidHom.mem_ker).1 hz))⟩

theorem liftSurj_apply {G T H : Type} [Group G] [Group T] [Group H] (π : G →* T)
    (hπ : Function.Surjective π) (f : G →* H) (hf : ∀ z, π z = 1 → f z = 1) (z : G) :
    liftSurj π hπ f hf (π z) = f z :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ z

theorem hom_ext_of_surj {G T H : Type} [Group G] [Group T] [Group H] (π : G →* T)
    (hπ : Function.Surjective π) (χ χ' : T →* H) (h : ∀ z, χ (π z) = χ' (π z)) : χ = χ' :=
  MonoidHom.ext fun t => by
    obtain ⟨z, rfl⟩ := hπ t
    exact h z

variable {R : Type} [CommRing R] {E : Type} [Field E] [NumberField E] {N : ℕ} {T : Type} [CommGroup T]

def charOf (m : ℕ) [NeZero m] (ζ : Rˣ) (hζ : ζ ^ m = 1) (π : Multiplicative (Fin N → 𝓞 E) →* T)
    (hπ : Function.Surjective π) (hker : ∀ y, π (Multiplicative.ofAdd y) = 1 ↔ ∃ y', y = m • y')
    (e : (Fin N → 𝓞 E) →+ (Fin N → 𝓞 E) →+ ZMod m) (y : Fin N → 𝓞 E) : T →* Rˣ :=
  liftSurj π hπ ((powChar m ζ hζ).comp (e y).toMultiplicative) (fun z hz => by
    obtain ⟨z', hz'⟩ := (hker (Multiplicative.toAdd z)).1 hz
    have h0 : e y (Multiplicative.toAdd z) = 0 := by
      rw [hz', map_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    show powChar m ζ hζ (Multiplicative.ofAdd (e y (Multiplicative.toAdd z))) = 1
    rw [h0, ofAdd_zero, map_one])

theorem charOf_apply (m : ℕ) [NeZero m] (ζ : Rˣ) (hζ : ζ ^ m = 1) (π : Multiplicative (Fin N → 𝓞 E) →* T)
    (hπ : Function.Surjective π) (hker : ∀ y, π (Multiplicative.ofAdd y) = 1 ↔ ∃ y', y = m • y')
    (e : (Fin N → 𝓞 E) →+ (Fin N → 𝓞 E) →+ ZMod m) (y z : Fin N → 𝓞 E) :
    charOf m ζ hζ π hπ hker e y (π (Multiplicative.ofAdd z)) = ζ ^ (e y z).val :=
  liftSurj_apply _ _ _ _ _

end GlobalTheory.CompanionTheory.Ar.BT.ChartEx

namespace GlobalTheory.CompanionTheory.Ar.BT.ChartEx

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField

variable {R : Type} [CommRing R] {E : Type} [Field E] [NumberField E] {N : ℕ} {T : Type} [CommGroup T]

section chars
variable (m : ℕ) [NeZero m] (ζ : Rˣ) (hζ : ζ ^ m = 1) (π : Multiplicative (Fin N → 𝓞 E) →* T)
    (hπ : Function.Surjective π) (hker : ∀ y, π (Multiplicative.ofAdd y) = 1 ↔ ∃ y', y = m • y')
    (e : (Fin N → 𝓞 E) →+ (Fin N → 𝓞 E) →+ ZMod m)

omit [NeZero m] in
theorem charOf_eq_iff (π : Multiplicative (Fin N → 𝓞 E) →* T)
    (hπ : Function.Surjective π) (χ χ' : T →* Rˣ) (h : ∀ z, χ (π (Multiplicative.ofAdd z)) = χ' (π (Multiplicative.ofAdd z))) :
    χ = χ' :=
  hom_ext_of_surj π hπ χ χ' fun z => h (Multiplicative.toAdd z)

theorem charOf_add (y y' : Fin N → 𝓞 E) :
    charOf m ζ hζ π hπ hker e (y + y') = charOf m ζ hζ π hπ hker e y * charOf m ζ hζ π hπ hker e y' :=
  charOf_eq_iff π hπ _ _ fun z => by
    rw [MonoidHom.mul_apply, charOf_apply, charOf_apply, charOf_apply, ← powChar_apply m ζ hζ,
      ← powChar_apply m ζ hζ, ← powChar_apply m ζ hζ, map_add, AddMonoidHom.add_apply, ofAdd_add, map_mul]

theorem charOf_zero : charOf m ζ hζ π hπ hker e 0 = 1 :=
  charOf_eq_iff π hπ _ _ fun z => by
    rw [MonoidHom.one_apply, charOf_apply, ← powChar_apply m ζ hζ, map_zero, AddMonoidHom.zero_apply,
      ofAdd_zero, map_one]

theorem charOf_neg (y : Fin N → 𝓞 E) :
    charOf m ζ hζ π hπ hker e (-y) = (charOf m ζ hζ π hπ hker e y)⁻¹ :=
  charOf_eq_iff π hπ _ _ fun z => by
    rw [MonoidHom.inv_apply, charOf_apply, charOf_apply, ← powChar_apply m ζ hζ,
      ← powChar_apply m ζ hζ, map_neg, AddMonoidHom.neg_apply, ofAdd_neg, map_inv]

def mulMap (b : 𝓞 E) : T →* T :=
  liftSurj π hπ (π.comp (DistribMulAction.toAddMonoidHom (Fin N → 𝓞 E) b).toMultiplicative) (fun z hz => by
    obtain ⟨z', hz'⟩ := (hker (Multiplicative.toAdd z)).1 hz
    show π (Multiplicative.ofAdd (b • Multiplicative.toAdd z)) = 1
    rw [hker, hz', smul_comm]
    exact ⟨_, rfl⟩)

theorem mulMap_apply (b : 𝓞 E) (z : Fin N → 𝓞 E) :
    mulMap m π hπ hker b (π (Multiplicative.ofAdd z)) = π (Multiplicative.ofAdd (b • z)) :=
  liftSurj_apply _ _ _ _ _

end chars

def dualAct {L : Type} [AddCommGroup L] [Module R L] (ρ : 𝓞 E →+* Module.End R L) (σ : 𝓞 E ≃+* 𝓞 E) :
    𝓞 E →+* Module.End R (Module.Dual R L) where
  toFun a := (ρ (σ a)).dualMap
  map_one' := by ext w l; simp
  map_mul' a b := by
    rw [mul_comm a b]
    ext w l
    simp [Module.End.mul_apply]
  map_zero' := by ext w l; simp
  map_add' a b := by ext w l; simp

theorem dualAct_apply {L : Type} [AddCommGroup L] [Module R L] (ρ : 𝓞 E →+* Module.End R L) (σ : 𝓞 E ≃+* 𝓞 E)
    (a : 𝓞 E) (w : Module.Dual R L) : dualAct ρ σ a w = w ∘ₗ ρ (σ a) := rfl

end GlobalTheory.CompanionTheory.Ar.BT.ChartEx

namespace GlobalTheory.CompanionTheory.Ar.BT.ChartEx

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField

theorem htChartExists : HTChartExists := by
  intro R K _ _ _ _ _ _ _ _ E _ _ c p n N _ T _ _ Γ S G _ _ x i hTor hSm act hmon L _ _ M ρ hρ Ω _ _ _ _ j hj
    π hπ hker hact ζ hζ e halt hadj hsurj hinj
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  have hpn : ((p ^ n : ℕ) : R) ≠ 0 := Nat.cast_ne_zero.2 (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  haveI : Smooth G.hom := hSm
  obtain ⟨hfin, hproj, -⟩ := GlobalTheory.T.lie_model_finite_base_change S G R x L M

  have hex : ∀ χ : T →* Rˣ, ∃ w, Γ.IsHT i M (p ^ n) χ w := fun χ =>
    GlobalTheory.T.exists_hodge_tate_functional R T Γ S G x (p ^ n) i hTor hSm L M χ
  have hadd : ∀ (χ χ' : T →* Rˣ) (w w' : Module.Dual R L), Γ.IsHT i M (p ^ n) χ w → Γ.IsHT i M (p ^ n) χ' w' →
      Γ.IsHT i M (p ^ n) (χ * χ') (w + w') := fun χ χ' w w' =>
    GlobalTheory.T.hodge_tate_functional_mul R T Γ S G x (p ^ n) i hTor L M χ χ' w w'
  have huniq : ∀ (χ : T →* Rˣ) (w w' : Module.Dual R L), Γ.IsHT i M (p ^ n) χ w →
      (Γ.IsHT i M (p ^ n) χ w' ↔ ∃ u : Module.Dual R L, w' = w + (p ^ n) • u) := fun χ w w' =>
    GlobalTheory.T.hodge_tate_functional_unique_mod_smul R T Γ S G x (p ^ n) i hTor hSm hpn L M χ w w'
  have hzero : Γ.IsHT i M (p ^ n) 1 0 := by
    obtain ⟨w, hw⟩ := hex 1
    have h2 := hadd 1 1 w w hw hw
    rw [_root_.mul_one] at h2
    obtain ⟨u, hu⟩ := (huniq 1 w (w + w) hw).1 h2
    refine (huniq 1 w 0 hw).2 ⟨-u, ?_⟩
    have : w = (p ^ n) • u := add_left_cancel hu
    rw [smul_neg, this, add_neg_cancel]
  have hneg : ∀ (χ : T →* Rˣ) (w : Module.Dual R L), Γ.IsHT i M (p ^ n) χ w → Γ.IsHT i M (p ^ n) χ⁻¹ (-w) := by
    intro χ w hw
    obtain ⟨w', hw'⟩ := hex χ⁻¹
    have h2 := hadd χ χ⁻¹ w w' hw hw'
    rw [_root_.mul_inv_cancel] at h2
    obtain ⟨u, hu⟩ := (huniq 1 0 (w + w') hzero).1 h2
    refine (huniq χ⁻¹ w' (-w) hw').2 ⟨-u, ?_⟩
    rw [zero_add] at hu
    rw [smul_neg, ← hu]
    abel

  let χ := charOf (p ^ n) ζ hζ π hπ hker e
  obtain ⟨b⟩ : Nonempty (Module.Basis (Module.Free.ChooseBasisIndex ℤ (Fin N → 𝓞 E)) ℤ (Fin N → 𝓞 E)) :=
    ⟨Module.Free.chooseBasis ℤ (Fin N → 𝓞 E)⟩
  choose wb hwb using fun k => hex (χ (b k))
  let h : (Fin N → 𝓞 E) →+ Module.Dual R L := (b.constr ℤ wb).toAddMonoidHom
  have hh : ∀ y, Γ.IsHT i M (p ^ n) (χ y) (h y) := by
    intro y
    have hy : y ∈ (Submodule.span ℤ (Set.range b)).toAddSubgroup := by
      rw [Submodule.mem_toAddSubgroup, b.span_eq]; exact Submodule.mem_top
    rw [Submodule.span_int_eq_addSubgroupClosure] at hy
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨k, rfl⟩ := hy
      have : h (b k) = wb k := by simp [h, Module.Basis.constr_basis]
      rw [this]; exact hwb k
    | zero => rw [map_zero, show χ 0 = 1 from charOf_zero _ _ _ _ _ _ _]; exact hzero
    | add y y' _ _ h1 h2 =>
      rw [map_add, show χ (y + y') = χ y * χ y' from charOf_add _ _ _ _ _ _ _ y y']; exact hadd _ _ _ _ h1 h2
    | neg y _ h1 => rw [map_neg, show χ (-y) = (χ y)⁻¹ from charOf_neg _ _ _ _ _ _ _ y]; exact hneg _ _ h1

  have hlin : ∀ (a : 𝓞 E) y, ∃ u, h (a • y) = dualAct ρ (RingOfIntegers.mapRingEquiv c) a (h y) + (p ^ n) • u := by
    intro a y
    have hαc : χ (a • y) = (χ y).comp (mulMap (p ^ n) π hπ hker (RingOfIntegers.mapRingEquiv c a)) :=
      charOf_eq_iff π hπ _ _ fun z => by
        rw [MonoidHom.comp_apply, mulMap_apply, charOf_apply, charOf_apply, hadj]
    have hαpt : ∀ t, (Γ.pt (mulMap (p ^ n) π hπ hker (RingOfIntegers.mapRingEquiv c a) t)).left ≫ i =
        (Γ.pt t).left ≫ i ≫ (act (RingOfIntegers.mapRingEquiv c a)).left := by
      intro t
      obtain ⟨z, rfl⟩ := hπ t
      have := mulMap_apply (p ^ n) π hπ hker (RingOfIntegers.mapRingEquiv c a) (Multiplicative.toAdd z)
      rw [ofAdd_toAdd] at this
      rw [this]
      exact hact _ _
    haveI := hmon (RingOfIntegers.mapRingEquiv c a)
    have h1 : Γ.IsHT i M (p ^ n) (χ (a • y)) (dualAct ρ (RingOfIntegers.mapRingEquiv c) a (h y)) := by
      rw [hαc, dualAct_apply]
      exact GlobalTheory.T.hodge_tate_functional_endomorphism R T Γ S G x (p ^ n) i hTor L M (act (RingOfIntegers.mapRingEquiv c a)) _
        (ρ (RingOfIntegers.mapRingEquiv c a)) hαpt (hρ _) (χ y) (h y) (hh y)
    obtain ⟨u, hu⟩ := (huniq _ _ _ (hh (a • y))).1 h1
    refine ⟨-u, ?_⟩
    rw [hu, smul_neg, add_neg_cancel_right]
  obtain ⟨D, hDom, hDe, hDh, hDρ⟩ := GlobalTheory.T.hodge_tate_lattice_base_change_pairing R K E c p n N (Module.Dual R L) Ω j hj
    (dualAct ρ (RingOfIntegers.mapRingEquiv c)) e h halt hadj hsurj hinj hlin
  refine ⟨D, hDe, hDom, fun a w => ?_, fun y => ⟨χ y, h y, fun z => ?_, hDh y, hh y⟩⟩
  · rw [hDρ]; rfl
  · rw [hDe]; exact charOf_apply _ _ _ _ _ _ _ _ _

end GlobalTheory.CompanionTheory.Ar.BT.ChartEx
