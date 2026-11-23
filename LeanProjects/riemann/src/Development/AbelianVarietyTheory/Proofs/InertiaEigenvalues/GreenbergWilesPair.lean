import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VecPairApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GreenbergWilesTotallyComplex
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelAllEquivSel
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalDualityFiniteDiscreteModules
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedDualEvalBidualApply
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardDualZmodModuleEqCard

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.PairFormula

theorem perp_iff {n : ℕ} [NeZero n] {Λ : Type} [CommRing Λ]
    {M : Type} [AddCommGroup M] [Module Λ M] [Module (ZMod n) M] [TopologicalSpace M]
    [DiscreteTopology M]
    {M' : Type} [AddCommGroup M'] [Module Λ M'] [TopologicalSpace M'] [DiscreteTopology M']
    {D Γ : Type} [Group D] [TopologicalSpace D] [Group Γ]
    (ρ : Representation Λ D M) (ρ' : Representation Λ D M') (P : M →+ M' →+ ZMod n)
    (μ : Γ →* (ZMod n)ˣ) (ρS : Representation (ZMod n) Γ M) (φ : D →* Γ)
    (hρ : ∀ g m, ρ g m = ρS (φ g) m) (hc : ContAction (ρS.comp φ)) (χ : D → ZMod n)
    (hχ : ∀ g, χ g = ((μ (φ g) : (ZMod n)ˣ) : ZMod n))
    (hP : ∀ g x y, P (ρ g x) (ρ' g y) = χ g * P x y)
    (L : Submodule Λ (H1 ρ)) (LS : Submodule (ZMod n) (H1 (ρS.comp φ)))
    (hL : ∀ (z : Z1 ρ) (z' : Z1 (ρS.comp φ)), (∀ g, z'.1 g = z.1 g) →
      (Submodule.Quotient.mk z ∈ L ↔ Submodule.Quotient.mk z' ∈ LS))
    (y : Z1 ρ') (y' : Z1 ((twDual μ ρS).comp φ)) (hy : ∀ g x, y'.1 g x = P x (y.1 g)) :
    (∀ x ∈ LS, cupH1H1TwistedDual μ ρS φ hc (Submodule.Quotient.mk y') x = 0) ↔
      ∀ x : Z1 ρ, Submodule.Quotient.mk x ∈ L → CupB χ (fun g m => ρ' g m) P x.1 y.1 := by
  let E := GlobalTheory.DualPairFormula.cocycleEquiv ρ (ρS.comp φ) (AddEquiv.refl M) hρ
  have hE : ∀ x g, (E x).1 g = x.1 g := fun _ _ => rfl
  have key : ∀ (x : Z1 ρ) g h, P (x.1 (g * h)) (y.1 (g * h)) = P (x.1 g) (y.1 g) +
      P (x.1 g) (ρ' g (y.1 h)) + P (ρ g (x.1 h)) (y.1 g) + χ g * P (x.1 h) (y.1 h) :=
    fun x g h => by
    rw [x.2.2, y.2.2, ← hP]
    simp only [map_add, AddMonoidHom.add_apply]
    ring
  have cb : ∀ x : Z1 ρ, Continuous fun g => P (x.1 g) (y.1 g) := fun x =>
    (continuous_of_discreteTopology (f := fun p : M × M' => P p.1 p.2)).comp
      (x.2.1.prodMk y.2.1)
  have hcup : ∀ x : Z1 ρ,
      cupH1H1TwistedDual μ ρS φ hc (Submodule.Quotient.mk y') (Submodule.Quotient.mk (E x)) = 0 ↔
      ∃ c : D → ZMod n, Continuous c ∧ ∀ g h,
        P (x.1 g) (ρ' g (y.1 h)) = χ g * c h - c (g * h) + c g := fun x => by
    have e0 : cupH1H1TwistedDual μ ρS φ hc (Submodule.Quotient.mk y') (Submodule.Quotient.mk (E x)) = 0 ↔
      ∃ c : D → ZMod n, Continuous c ∧ ∀ g h,
        χ g * c h - c (g * h) + c g = P (ρ g (x.1 h)) (y.1 g) := by
      refine (Submodule.Quotient.mk_eq_zero _).trans ((separated_dvr_second_cohomology_mem _ _).trans ?_)
      refine exists_congr fun c => and_congr_right fun _ => ?_
      rw [funext_iff, Prod.forall]
      refine forall_congr' fun g => forall_congr' fun h => ?_
      rw [← hy, hρ, hχ]
      exact Iff.rfl
    rw [e0]
    constructor
    · rintro ⟨c, hc1, hc2⟩
      refine ⟨fun g => -c g - P (x.1 g) (y.1 g), hc1.neg.sub (cb x), fun g h => ?_⟩
      linear_combination hc2 g h - key x g h
    · rintro ⟨c, hc1, hc2⟩
      refine ⟨fun g => -c g - P (x.1 g) (y.1 g), hc1.neg.sub (cb x), fun g h => ?_⟩
      linear_combination hc2 g h + key x g h
  constructor
  · intro H x hx
    obtain ⟨c, hc1, hc2⟩ := (hcup x).1 (H _ ((hL _ _ (hE _)).1 hx))
    exact ⟨c, (IsLocallyConstant.iff_continuous c).2 hc1, hc2⟩
  · intro H x hx
    induction x using Submodule.Quotient.induction_on with | H x =>
    obtain ⟨x, rfl⟩ := E.surjective x
    obtain ⟨f, hf1, hf2⟩ := H x ((hL _ _ (hE _)).2 hx)
    exact (hcup x).2 ⟨f, hf1.continuous, hf2⟩

open GlobalTheory.DualPairFormula GlobalTheory.SelInf in

theorem greenbergWiles_pair : PoitouTateTotallyComplex → LocalFiniteness → GlobalFiniteness → GlobalEulerChar → ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyComplex F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (Λ : Type) [CommRing Λ] (W : Type) [AddCommGroup W] [Module Λ W] [TopologicalSpace W] [DiscreteTopology W] [Finite W] (W' : Type) [AddCommGroup W'] [Module Λ W'] [TopologicalSpace W'] [DiscreteTopology W'] [Finite W'] (ρ : Representation Λ (G F Ω) W) (ρ' : Representation Λ (G F Ω) W') (P : W →+ W' →+ ZMod (l ^ n)), 0 < n → ContAction ρ → ContAction ρ' → (∀ x, (∀ y, P x y = 0) → x = 0) → (∀ y, (∀ x, P x y = 0) → y = 0) → (∀ g x y, P (ρ g x) (ρ' g y) = ((cycMod F Ω l n g : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) * P x y) → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (A : Formalism.GaloisCohomology.Places F Ω), ContainsAbove S l → (∀ v ∉ S, ∀ B : ValuationSubring Ω, IsPlaceOver B v → ∀ τ ∈ Ine (F := F) B, ρ τ = 1 ∧ ρ' τ = 1) → ∀ (L : ∀ v, Submodule Λ (H1 (ρ.comp (Dec (F := F) (A.1 v)).subtype))), (∀ v ∉ S, L v = Formalism.GaloisCohomology.unrAt ρ (A.1 v)) → ∀ C : Set (H1 ρ'), (∀ y : Z1 ρ', Submodule.Quotient.mk y ∈ C ↔ (∀ v ∉ S, ∀ τ ∈ Ine (F := F) (A.1 v), y.1 τ = 0) ∧ ∀ v ∈ S, ∀ x : Z1 (ρ.comp (Dec (F := F) (A.1 v)).subtype), Submodule.Quotient.mk x ∈ L v → CupB (fun g : Dec (F := F) (A.1 v) => ((cycMod F Ω l n g.1 : (ZMod (l ^ n))ˣ) : ZMod (l ^ n))) (fun g m => ρ' g.1 m) P x.1 (fun g => y.1 g.1)) → Finite C ∧ Nat.card (Formalism.GaloisCohomology.SelAll ρ A L) * Nat.card (H0 ρ') * (∏ v ∈ S, Nat.card (H0 (ρ.comp (Dec (F := F) (A.1 v)).subtype))) * Nat.card W ^ InfinitePlace.nrComplexPlaces F = Nat.card C * Nat.card (H0 ρ) * ∏ v ∈ S, Nat.card (L v) := by
  intro hPT hLF hGF hEC F Ω _ _ _ _ _ _ l _ n Λ _ W _ _ _ _ _ W' _ _ _ _ _ ρ ρ' P hn hρ hρ' h1 h2 hP
    S A hS hur L hL C hC
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hk : ∀ (x : W) (y : W'), (l ^ n) • P x y = 0 := fun x y => by
    rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  haveI : Module (ZMod (l ^ n)) W := AddCommGroup.zmodModule fun x => h1 _ fun y => by
    rw [map_nsmul, AddMonoidHom.nsmul_apply, hk]
  haveI : Module (ZMod (l ^ n)) W' := AddCommGroup.zmodModule fun y => h2 _ fun x => by
    rw [map_nsmul, hk]
  obtain ⟨ρS, hρS, hd⟩ := exists_descent (zmodRep (l ^ n) ρ) hρ (S : Set _)
    fun v hv B hB σ hσ => by
      ext x
      change ρ σ x = x
      rw [(hur v hv B hB σ hσ).1]
      rfl
  replace hd : ∀ (g : G F Ω) (x : W), ρ g x = ρS (toGS Ω (S : Set (HeightOneSpectrum (𝓞 F))) g) x := hd
  obtain ⟨μ, hμ⟩ := PoitouTate.exists_lift_cycMod (Ω := Ω) (r := n) hS
  have hμ' : ∀ g, ((cycMod F Ω l n g : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) =
      ((μ (toGS Ω _ g) : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) := fun g => by rw [← hμ]; rfl
  have hfin : Finite (TDual (ZMod (l ^ n)) W) := GlobalTheory.DualSide.finite_TDual
  have hfin' : Finite (TDual (ZMod (l ^ n)) W') := GlobalTheory.DualSide.finite_TDual
  let f : W' →+ TDual (ZMod (l ^ n)) W := AddMonoidHom.mk'
    (fun y => TDual.mk ((P.flip y).toZModLinearMap (l ^ n))) (fun y y' => by ext x; simp)
  have hf : ∀ y x, f y x = P x y := fun _ _ => rfl
  have inj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    refine h2 y fun x => ?_
    rw [← hf, hy]
    rfl
  have c1 : Nat.card (TDual (ZMod (l ^ n)) W) = Nat.card W := GlobalTheory.ZModDual.card_dual_eq _ W
  have c2 : Nat.card (TDual (ZMod (l ^ n)) W') = Nat.card W' := GlobalTheory.ZModDual.card_dual_eq _ W'
  have c3 : Nat.card W ≤ Nat.card W' := by
    rw [← c2]
    refine Nat.card_le_card_of_injective
      (fun x => TDual.mk ((P x).toZModLinearMap (l ^ n))) fun x x' hxx' => ?_
    have : ∀ y, P x y = P x' y := fun y =>
      congrArg (fun φ : TDual (ZMod (l ^ n)) W' => φ y) hxx'
    exact sub_eq_zero.1 (h1 _ fun y => by rw [map_sub, AddMonoidHom.sub_apply, this, sub_self])
  let e : W' ≃+ TDual (ZMod (l ^ n)) W :=
    AddEquiv.ofBijective f (inj.bijective_of_nat_card_le (c1 ▸ c3))
  have he : ∀ y x, e y x = P x y := fun _ _ => rfl
  have hee : ∀ g y, e (ρ' g y) = twDual μ ρS (toGS Ω _ g) (e y) := fun g y => by
    ext x
    rw [twDual_apply, he, he, ← map_inv, ← hd, ← hμ', ← hP, ← Module.End.mul_apply, ← map_mul,
      mul_inv_cancel, map_one, Module.End.one_apply]
  have hex := fun v : S => exists_transport_cond (ρ.comp (Dec (F := F) (A.1 v.1)).subtype)
    (ρS.comp (locFam S (fun v => A.1 v.1) v)) (AddEquiv.refl W) (fun g x => hd g x) (L v.1)
  choose LS hLS1 hLS2 using hex
  obtain ⟨f1, f2, hmain⟩ := GlobalTheory.GWComplex.greenbergWiles_totallyComplex hPT hLF hGF hEC F Ω l n W S
    ρS hn hS hρS μ hμ (fun v => A.1 v.1) (fun v => A.2 v.1) LS
  obtain ⟨E1⟩ := selAll_equiv_sel F Ω Λ (ZMod (l ^ n)) W W S A ρ ρS (AddEquiv.refl W) hρ hd L LS
    hL hLS2

  have hv' : ∀ (z : Z1 (twDual μ ρS)) (v : S),
      resH1 (twDual μ ρS) (locFam S (fun v => A.1 v.1) v) (continuous_locFam S _ v)
        (Submodule.Quotient.mk z) ∈ perpCond μ ρS (locFam S fun v => A.1 v.1)
          (fun v => hρS.comp' (continuous_locFam S _ v)) LS v ↔
      ∀ x : Z1 (ρ.comp (Dec (F := F) (A.1 v.1)).subtype), Submodule.Quotient.mk x ∈ L v.1 →
        CupB (fun g : Dec (F := F) (A.1 v.1) => ((cycMod F Ω l n g.1 : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)))
          (fun g m => ρ' g.1 m) P x.1 (fun g => (infZ e hee z).1 g.1) := fun z v => by
    rw [mem_perpCond]
    exact perp_iff (ρ.comp (Dec (F := F) (A.1 v.1)).subtype) (ρ'.comp (Dec (F := F) (A.1 v.1)).subtype)
      P μ ρS (locFam S (fun v => A.1 v.1) v) (fun g x => hd g x) _
      (fun g => ((cycMod F Ω l n g.1 : (ZMod (l ^ n))ˣ) : ZMod (l ^ n))) (fun g => hμ' g.1)
      (fun g => hP g.1) (L v.1) (LS v) (hLS2 v)
      (restrictCocycles1 ρ' (Dec (F := F) (A.1 v.1)).subtype continuous_subtype_val (infZ e hee z))
      (restrictCocycles1 (twDual μ ρS) (locFam S (fun v => A.1 v.1) v) (continuous_locFam S _ v) z)
      (fun g x => by
        change z.1 (toGS Ω _ g.1) x = P x (e.symm (z.1 (toGS Ω _ g.1)))
        rw [← he, e.apply_symm_apply])
  have hmem : ∀ z : Z1 (twDual μ ρS),
      Submodule.Quotient.mk z ∈ Sel (twDual μ ρS) (locFam S fun v => A.1 v.1) (continuous_locFam S _)
        (perpCond μ ρS (locFam S fun v => A.1 v.1) (fun v => hρS.comp' (continuous_locFam S _ v)) LS) ↔
      Submodule.Quotient.mk (infZ e hee z) ∈ C := fun z => by
    rw [mem_Sel, hC]
    constructor
    · intro h
      refine ⟨fun v hv σ hσ => ?_, fun v hv x hx => (hv' z ⟨v, hv⟩).1 (h ⟨v, hv⟩) x hx⟩
      have : toGS Ω (S : Set (HeightOneSpectrum (𝓞 F))) σ = 1 :=
        (QuotientGroup.eq_one_iff σ).2 (Ine_le_NS (by simpa using hv) (A.2 v) hσ)
      rw [infZ_apply, this, z_one, map_zero]
    · rintro ⟨-, h⟩ v
      exact (hv' z v).2 (h v.1 v.2)
  have hmem' : ∀ x : H1 (twDual μ ρS),
      x ∈ Sel (twDual μ ρS) (locFam S fun v => A.1 v.1) (continuous_locFam S _)
        (perpCond μ ρS (locFam S fun v => A.1 v.1) (fun v => hρS.comp' (continuous_locFam S _ v)) LS) ↔
      infH e hee x ∈ C := fun x => by
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [infH_mk]
    exact hmem z
  let T := Equiv.ofBijective (fun x : Sel (twDual μ ρS) (locFam S fun v => A.1 v.1)
      (continuous_locFam S _) (perpCond μ ρS (locFam S fun v => A.1 v.1)
        (fun v => hρS.comp' (continuous_locFam S _ v)) LS) =>
      (⟨infH e hee x.1, (hmem' _).1 x.2⟩ : C)) ⟨fun x y h => ?_, fun y => ?_⟩
  · have hs : Function.Surjective (toGS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) :=
      QuotientGroup.mk'_surjective _
    refine ⟨Finite.of_equiv _ T, ?_⟩
    rw [Nat.card_congr E1, ← Nat.card_congr T, ← card_H0_eq_of_equivariant_equiv ρ' _ _ hs e hee,
      ← card_H0_eq_of_equivariant_equiv ρ ρS _ hs (AddEquiv.refl W) hd, ← Finset.prod_coe_sort S, ← Finset.prod_coe_sort S]
    simp only [← hLS1]
    rw [← hmain]
    congr 2
    refine Finset.prod_congr rfl fun v _ => ?_
    exact (card_H0_eq_of_equivariant_equiv (ρ.comp (Dec (F := F) (A.1 v.1)).subtype)
      (ρS.comp (locFam S (fun v => A.1 v.1) v)) id Function.surjective_id (AddEquiv.refl W)
      (fun g x => hd g x)).symm
  · exact Subtype.ext (infH_injective e hee (congrArg Subtype.val h))
  · obtain ⟨y, hy⟩ := y
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨z', rfl⟩ := exists_infZ e hee z (vanish_NS e hee A z ((hC z).1 hy).1)
    exact ⟨⟨Submodule.Quotient.mk z', (hmem' _).2 (by rw [infH_mk]; exact hy)⟩,
      Subtype.ext (infH_mk e hee z')⟩

end GlobalTheory.PairFormula
