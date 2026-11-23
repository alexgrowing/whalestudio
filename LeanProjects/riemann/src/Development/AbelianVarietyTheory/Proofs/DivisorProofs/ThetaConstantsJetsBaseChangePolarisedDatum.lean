import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KeyPBIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeyDatumBaseChangeThetaJets
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocGenOfTrivial

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.JetBCGen

open TrivSqZeroExt

theorem spMap_comp_gen {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (a : A →+* B) (b : C →+* A) :
    spMap a ≫ spMap b = spMap (a.comp b) := by
  rw [spMap, spMap, spMap, ← Spec.map_comp]
  rfl

theorem surj_fst (R : Type) [CommRing R] : Function.Surjective (spMap (TrivSqZeroExt.fstHom R R R).toRingHom) := by
  have hs : Function.Surjective (TrivSqZeroExt.fstHom R R R).toRingHom := fun x => ⟨TrivSqZeroExt.inl x, rfl⟩
  intro P
  have : P ∈ Set.range (PrimeSpectrum.comap (TrivSqZeroExt.fstHom R R R).toRingHom) := by
    rw [range_comap_of_surjective _ _ hs]
    intro x hx
    refine (P : PrimeSpectrum (DualNumber R)).2.mem_of_pow_mem 2 ?_
    have hx' : x.fst = 0 := hx
    have : x ^ 2 = 0 := by ext <;> simp [sq, hx']
    rw [this]; exact zero_mem _
  exact this

theorem isLocalRing_dual (k : Type) [Field k] : IsLocalRing (DualNumber k) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => by
    by_cases h : TrivSqZeroExt.fst x = 0
    · right
      rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
      simp [h]
    · left
      rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
      exact isUnit_iff_ne_zero.2 h

theorem map_inl_inr {R K : Type} [CommRing R] [CommRing K] (f : R →+* K) (F : DualNumber R →+* DualNumber K)
    (hF1 : ∀ a, F (algebraMap R _ a) = algebraMap K _ (f a)) (hF2 : F DualNumber.eps = DualNumber.eps) (a b : R) :
    F (inl a) = inl (f a) ∧ F (inr b) = inr (f b) := by
  have h1 : ∀ a, F (inl a) = inl (f a) := fun a => by
    have := hF1 a
    rwa [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.algebraMap_eq_inl] at this
  refine ⟨h1 a, ?_⟩
  have e : ∀ {S : Type} [CommRing S] (c : S), (inr c : DualNumber S) = inl c * DualNumber.eps := fun c => by
    rw [DualNumber.eps, TrivSqZeroExt.inl_mul_inr, smul_eq_mul, _root_.mul_one]
  rw [e, map_mul, h1, hF2, ← e]

theorem valR_spMap_comp' {A A' : Type} [CommRing A] [CommRing A'] {Y : Scheme.{0}} (ψ : A →+* A') (x : Sp A ⟶ Y)
    (V : Y.Opens) (h : ⊤ ≤ x ⁻¹ᵁ V) (f : Γ(Y, V)) : valR (spMap ψ ≫ x) V f = ψ (valR x V f) := by
  have h' : ⊤ ≤ (spMap ψ ≫ x) ⁻¹ᵁ V := fun y _ => h (Set.mem_univ ((spMap ψ) y))
  unfold valR
  rw [dif_pos h', dif_pos h]
  have e : (spMap ψ ≫ x).appLE V ⊤ h' = x.appLE V ⊤ h ≫ (spMap ψ).appTop :=
    (Scheme.Hom.appLE_comp_appLE (spMap ψ) x V ⊤ ⊤ h le_rfl).symm
  have n := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ψ)
  change ((spMap ψ ≫ x).appLE V ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of A')).hom).hom f =
    (x.appLE V ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom ≫ CommRingCat.ofHom ψ).hom f
  rw [e, Category.assoc, n]

end GlobalTheory.MBLow.JetBCGen

namespace GlobalTheory.MBLow.JetBCGen

open GlobalTheory.ThetaPtMove

theorem pow_eq_one_of_gen {K : Type} [Field K] (P : PolAV (Sp K)) (k : ℕ) {T : Over (Sp K)} (x : T ⟶ P.A)
    (α : LB.Gen (thetaLB P.A P.L ((k : ℕ) : ℤ) x)) (hα : α.IsGen) : x ^ k = 1 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact pow_zero x
  refine (GlobalTheory.abelianSchemeLaws_all.1.kerPow (Sp K) P k hk T x).1 fun p => ⟨⊤, trivial, ?_⟩
  exact (GlobalTheory.KerPow.pull_iff _ _ _).2 (GlobalTheory.KerPow.HasGen.pull ⟨α, hα⟩ _ fun _ => rfl)

end GlobalTheory.MBLow.JetBCGen

namespace GlobalTheory.MBLow.JetBCGen

open GlobalTheory.MBLow.JetBC

theorem gs_theta {X X' : Scheme.{0}} {L₀ : LB X} {L₁ : LB X'} {φ : X' ⟶ X} (w : LB.Iso L₁ (L₀.pull φ))
    (θ₀ : L₀.Sec) (θ : L₁.Sec)
    (H : ∀ (j : (L₀.pull φ).ι) (i : L₁.ι) (h : (L₀.pull φ).U j ⊓ L₁.U i ≤ φ ⁻¹ᵁ L₀.U (j PUnit.unit)),
      (φ.appLE _ _ h).hom (θ₀.f (j PUnit.unit)) =
        (show Γ(X', (L₀.pull φ).U j ⊓ L₁.U i) from (w.s (j, i)).val) * resG _ inf_le_right (θ.f i))
    (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) (j : L₀.ι) (k : L₁.ι) (hj : φ (r z) ∈ L₀.U j) (hk : r z ∈ L₁.U k) :
    gs (r ≫ φ) z _ (θ₀.f j) = (gw w r z j k).val * gs r z _ (θ.f k) := by
  have hV : r z ∈ (L₀.pull φ).U (fun _ => j) ⊓ L₁.U k := ⟨mem_pull.2 hj, hk⟩
  have hle : (L₀.pull φ).U (fun _ => j) ⊓ L₁.U k ≤ φ ⁻¹ᵁ L₀.U j := fun y hy => mem_pull.1 hy.1
  rw [← gs_appLE' φ _ _ hle r z hV, H (fun _ => j) k hle, gs_mul _ _ _ hV]
  congr 1
  · exact gs_unit r z _ hV (w.s (fun _ => j, k))
  · exact gs_res _ _ _ hV _

end GlobalTheory.MBLow.JetBCGen

namespace GlobalTheory.MBLow.JetBCGen

open GlobalTheory.MBLow.JetBC GlobalTheory.ThetaPtMove GlobalTheory.ConstFam GlobalTheory.GlobalLift

theorem one_left_eq {S : Scheme.{0}} (A : Over S) [GrpObj A] (T : Over S) : (1 : T ⟶ A).left = T.hom ≫ eSec A := by
  show (toUnit T ≫ η[A]).left = _
  rw [Over.comp_left]
  rfl

theorem tr_move_gen {S S' : Scheme.{0}} {P₀ : PolAV S} {P : PolAV S'} {f : S' ⟶ S} {φ : P.A.left ⟶ P₀.A.left}
    (hp : IsGrpPullback P.A P₀.A f φ) {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left)
    (hτ : τ ≫ T₀.hom = T.hom ≫ f) {w : LB.Iso P.L (P₀.L.pull φ)}
    {ρ₀ : LB.Gen (P₀.L.pull (eSec P₀.A))} {ρ : LB.Gen (P.L.pull (eSec P.A))}
    (hw : w.IsGen) (he : eSec P.A ≫ φ = f ≫ eSec P₀.A)
    (hρ : PMaps w (fun _ : PUnit => eSec P.A) (fun _ => eSec P₀.A) (fun _ => 1) ρ ρ₀ f) {m : ℕ}
    {th₀ th t₀ t} (h : SecRel hp τ hτ w th th₀) (ht : SecRel hp τ hτ w t t₀) {U₀ U}
    (hU : ∀ s₀ s₀' s s', SecRel hp τ hτ w s s₀ → SecRel hp τ hτ w s' s₀' →
      IsActOf P₀.A P₀.L ((m ^ 2 : ℕ) : ℤ) U₀ s₀ s₀' → IsActOf P.A P.L ((m ^ 2 : ℕ) : ℤ) U s s')
    (H : Tr P₀ ρ₀ m th₀ U₀ t₀) : Tr P ρ m th U t := by
  obtain ⟨α₀, s₀, hα₀, hn, h₁, h₂⟩ := H
  obtain ⟨α, hα, v⟩ := exists_genThrough₂ hp τ hτ hw P₀.isLB P.isLB (psi_pow hp τ hτ m) α₀ hα₀
  obtain ⟨s, hs⟩ := exists_secRel hp τ hτ hw P₀.isLB P.isLB s₀
  refine ⟨α, s, hα, corr_of_val P.isLB fun y J' hJ' => ?_,
    isTwistPull_move hp τ hτ P₀.isLB P.isLB (psi_pow hp τ hτ m) hα v h hs h₁, hU _ _ _ _ hs ht h₂⟩
  obtain ⟨J, hJ⟩ := exists_good' P₀.isLB y
  have q := val_corr hJ hn (𝟙 _ ≫ τ)
  have q₁ := v _ (𝟙 _ ≫ (ptSecT P.A (1 : T ⟶ P.A)).left) y J J' hJ hJ'
  rw [Category.assoc, psi_ptSec hp τ hτ (over_one hp τ hτ), ← Category.assoc] at q₁
  have q₂ := pmaps_val (fun _ => he) hρ (𝟙 _ ≫ T.hom) hJ hJ'
  rw [Fintype.prod_unique] at q₂
  rw [val_pull hJ, val_rigT' _ _ _ _ _ _ _ _ hJ, Category.assoc _ τ T₀.hom, hτ, ← Category.assoc, q₁, q₂] at q
  rw [val_pull hJ', val_rigT' _ _ _ _ _ _ _ _ hJ']
  have e₁ : (𝟙 _ ≫ (ptSecT P.A (1 : T ⟶ P.A)).left) ≫ (snd T P.A).left = (𝟙 _ ≫ T.hom) ≫ eSec P.A := by
    rw [Category.id_comp, ptSecT_snd, one_left_eq, Category.id_comp]
  have e₂ : (𝟙 _ ≫ (ptSecT P.A (1 : T ⟶ P.A)).left) ≫ (snd T P.A ^ m).left = (𝟙 _ ≫ T.hom) ≫ eSec P.A := by
    rw [Category.id_comp, ← Over.comp_left, MonObj.comp_pow, ← e₁, Category.id_comp, ← Over.comp_left,
      show ptSecT P.A (1 : T ⟶ P.A) ≫ snd T P.A = 1 from lift_snd _ _, one_pow]
  rw [e₁, e₂] at q
  rw [zpow_one, mul_zpow, ← zpow_add] at q
  have e₃ : ((m ^ 2 : ℕ) : ℤ) + -((1 : ℕ) : ℤ) = ((m ^ 2 : ℕ) : ℤ) - 1 := by push_cast; ring
  rw [e₃] at q
  exact mul_left_cancel q

end GlobalTheory.MBLow.JetBCGen

namespace GlobalTheory.MBLow.JetBCGen

open TrivSqZeroExt

theorem one_add_inr_pow {K : Type} [Field K] (e : K) (M : ℕ) :
    ((1 : DualNumber K) + inr e) ^ M = 1 + inr ((M : K) * e) := by
  induction M with
  | zero => ext <;> simp
  | succ n ih => rw [pow_succ, ih]; ext <;> simp <;> ring

theorem dual_solve {K : Type} [Field K] (M : ℕ) (u₁ T' : DualNumber K) (u₀ r a b : K) (hu : u₁.fst = u₀)
    (h0 : u₀ ≠ 0) (h : u₁ ^ M * T' = inl ((u₀ * r) ^ M) * (inl a + inr b)) :
    T' = inl (r ^ M) * (inl a + inr (b - (M : K) * (u₁.snd / u₀) * a)) := by
  have hv : u₁ = inl u₀ * (1 + inr (u₁.snd / u₀)) := by
    ext
    · simp [hu]
    · simp [hu]; field_simp
  rw [hv, mul_pow, one_add_inr_pow, mul_pow, inl_mul, inl_pow, _root_.mul_assoc, _root_.mul_assoc] at h
  have hu0 : IsUnit (inl (u₀ ^ M) : DualNumber K) := by
    refine ⟨⟨inl (u₀ ^ M), inl ((u₀ ^ M)⁻¹), ?_, ?_⟩, rfl⟩ <;>
      rw [← inl_mul] <;> simp [pow_ne_zero M h0]
  have h' := hu0.mul_left_cancel h
  have hinv : (1 - inr ((M : K) * (u₁.snd / u₀)) : DualNumber K) * (1 + inr ((M : K) * (u₁.snd / u₀))) = 1 := by
    ext <;> simp
  calc T' = (1 - inr ((M : K) * (u₁.snd / u₀))) * ((1 + inr ((M : K) * (u₁.snd / u₀))) * T') := by
        rw [← _root_.mul_assoc, hinv, _root_.one_mul]
    _ = _ := by rw [h']; ext <;> simp <;> ring

end GlobalTheory.MBLow.JetBCGen

namespace GlobalTheory.MBLow.JetBCGen

open GlobalTheory.MBLow.JetBC GlobalTheory.ThetaPtMove GlobalTheory.ConstFam GlobalTheory.GlobalLift GlobalTheory.ZH.ThetaData

theorem valR_secRel {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A] {f : S' ⟶ S}
    {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ) {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left)
    (hτ : τ ≫ T₀.hom = T.hom ≫ f) {L₀ : LB G.left} {L₁ : LB A.left} {w : LB.Iso L₁ (L₀.pull φ)}
    (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) {k : ℕ} {t₀ : LB.Sec (LPow G L₀ (k : ℤ) T₀)} {t : LB.Sec (LPow A L₁ (k : ℤ) T)}
    (ht : SecRel hp τ hτ w t t₀) {C : Type} [CommRing C] [IsLocalRing C] (y : Sp C ⟶ (T ⊗ A).left)
    (j : L₀.ι) (i : L₁.ι) (hj : φ ((y ≫ (snd T A).left) (IsLocalRing.closedPoint C)) ∈ L₀.U j)
    (hi : (y ≫ (snd T A).left) (IsLocalRing.closedPoint C) ∈ L₁.U i) :
    valR (y ≫ psi hp τ hτ) ((LPow G L₀ (k : ℤ) T₀).U fun _ => j) (t₀.f fun _ => j) =
      valR (y ≫ (snd T A).left) _ (w.s (fun _ => j, i)).val ^ k *
        valR y ((LPow A L₁ (k : ℤ) T).U fun _ => i) (t.f fun _ => i) := by
  have e₀ : (y ≫ psi hp τ hτ) ≫ (snd T₀ G).left = (y ≫ (snd T A).left) ≫ φ := by
    rw [Category.assoc, Category.assoc, psi_snd']
  have m₀ : (y ≫ psi hp τ hτ) (IsLocalRing.closedPoint C) ∈ (LPow G L₀ (k : ℤ) T₀).U fun _ => j :=
    Set.mem_iInter.2 fun _ => by
      show ((y ≫ psi hp τ hτ) ≫ (snd T₀ G).left) (IsLocalRing.closedPoint C) ∈ L₀.U j
      rw [e₀]; exact hj
  have m₁ : y (IsLocalRing.closedPoint C) ∈ (LPow A L₁ (k : ℤ) T).U fun _ => i := Set.mem_iInter.2 fun _ => hi
  have mW : (y ≫ (snd T A).left) (IsLocalRing.closedPoint C) ∈ ((L₀.pull φ).div L₁).U (fun _ => j, i) :=
    ⟨mem_pull.2 hj, hi⟩
  obtain ⟨J', hJ', e'⟩ := exists_good L₁ hL₁ (IsLocalRing.closedPoint C) (fun _ : Unit => y ≫ (snd T A).left)
    (fun _ => i) (fun _ _ _ => rfl) (fun _ => hi)
  obtain ⟨J, hJ, e⟩ := exists_good L₀ hL₀ (IsLocalRing.closedPoint C)
    (fun _ : Unit => (y ≫ (snd T A).left) ≫ φ) (fun _ => j) (fun _ _ _ => rfl) (fun _ => hj)
  have q := ht _ y (IsLocalRing.closedPoint C) J J' hJ hJ'
  have q₀ := (sval_of (φ := fun _ : Fin 1 => (snd T₀ G).left) (ε := fun _ => (k : ℤ)) t₀ _ _ J (fun _ => j)
      (fun _ => by rw [e₀]; exact e ())).symm.trans (q.trans (congrArg (_ * ·)
    (sval_of (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => (k : ℤ)) t _ _ J' (fun _ => i)
      (fun _ => e' ()))))
  clear q
  have hw : GlobalTheory.ConstFam.wVal w (IsLocalRing.closedPoint C) J J' (y ≫ (snd T A).left) =
      gw w (y ≫ (snd T A).left) (IsLocalRing.closedPoint C) j i := by
    show gw w (y ≫ (snd T A).left) (IsLocalRing.closedPoint C) (J _) (J' _) = _
    rw [e (), e' ()]
  rw [valR_eq_gs _ _ m₀, valR_eq_gs _ _ m₁, valR_eq_gs _ _ mW, ← map_pow, ← map_mul]
  congr 1
  refine q₀.trans ?_
  rw [hw, gs_unit _ _ _ mW, zpow_natCast, Units.val_pow_eq_pow_val]
  rfl

end GlobalTheory.MBLow.JetBCGen

namespace GlobalTheory.MBLow.JetBCGen

open GlobalTheory.MBLow.JetBC GlobalTheory.ThetaPtMove GlobalTheory.ZH.ThetaData

theorem valR_rigRel {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A] {f : S' ⟶ S}
    {φ : A.left ⟶ G.left} {L₀ : LB G.left} {L₁ : LB A.left} {w : LB.Iso L₁ (L₀.pull φ)}
    {ρ₀ : LB.Gen (L₀.pull (eSec G))} {ρ : LB.Gen (L₁.pull (eSec A))}
    (he : eSec A ≫ φ = f ≫ eSec G)
    (hρ : PMaps w (fun _ : PUnit => eSec A) (fun _ => eSec G) (fun _ => 1) ρ ρ₀ f)
    {C : Type} [CommRing C] [IsLocalRing C] (s : Sp C ⟶ S') (j : L₀.ι) (i : L₁.ι)
    (hj : φ ((s ≫ eSec A) (IsLocalRing.closedPoint C)) ∈ L₀.U j)
    (hi : (s ≫ eSec A) (IsLocalRing.closedPoint C) ∈ L₁.U i) :
    valR (s ≫ f) ((L₀.pull (eSec G)).U fun _ => j) (ρ₀.s fun _ => j).val =
      valR (s ≫ eSec A) _ (w.s (fun _ => j, i)).val * valR s ((L₁.pull (eSec A)).U fun _ => i) (ρ.s fun _ => i).val := by
  have q := hρ _ s (IsLocalRing.closedPoint C) (fun _ => j) (fun _ => i) (fun _ => hj) (fun _ => hi)
  rw [Fintype.prod_unique, zpow_one] at q
  have mW : (s ≫ eSec A) (IsLocalRing.closedPoint C) ∈ ((L₀.pull φ).div L₁).U (fun _ => j, i) :=
    ⟨mem_pull.2 hj, hi⟩
  have m₁ : s (IsLocalRing.closedPoint C) ∈ (L₁.pull (eSec A)).U fun _ => i := mem_pull.2 hi
  have m₀ : (s ≫ f) (IsLocalRing.closedPoint C) ∈ (L₀.pull (eSec G)).U fun _ => j := by
    refine mem_pull.2 ?_
    show ((s ≫ f) ≫ eSec G) (IsLocalRing.closedPoint C) ∈ L₀.U j
    rw [Category.assoc, ← he, ← Category.assoc]
    exact hj
  rw [valR_eq_gs _ _ m₀, valR_eq_gs _ _ mW, valR_eq_gs _ _ m₁, ← map_mul]
  congr 1
  rw [gs_unit _ _ _ m₀, gs_unit _ _ _ mW, gs_unit _ _ _ m₁, ← Units.val_mul]
  exact congrArg Units.val q

end GlobalTheory.MBLow.JetBCGen

open GlobalTheory.MBLow.JetBC GlobalTheory.ThetaPtMove GlobalTheory.MBLow.JetBCGen TrivSqZeroExt in

theorem GlobalTheory.MBLow.thJet_of_keyAtMap : ∀ (R K : Type) [CommRing R] [Field K] (f : R →+* K) (x : KeyIn R) (x' : KeyIn K) (φ : x'.P.A.left ⟶ x.P.A.left), KeyAtMap x' x f φ → ∀ (g : ℕ) (hg : x.P.g = g) (hg' : x'.P.g = g) (m : ℕ) (I : Type) (pt : I → (baseOver (Sp R) ⟶ x.P.A)) (pt' : I → (baseOver (Sp K) ⟶ x'.P.A)) (ϑ : I → R) (J : I → Fin g → R), (∀ i, (pt' i).left ≫ φ = spMap f ≫ (pt i).left) → ThJet x hg m pt ϑ J → ThJet x' hg' m pt' (fun i => f (ϑ i)) (fun i j => f (J i j)) := by
  intro R K _ _ f x x' φ hK g hg hg' m I pt pt' ϑ J hpt ⟨th, hth, H⟩
  obtain ⟨he, w, hgg, F, hp, hw, hrig, hθ, hF1, hF2, hv⟩ := hK
  have := x'.P.isAb.comm
  haveI : IsLocalRing (DualNumber K) := isLocalRing_dual K
  let τ : (baseOver (Sp K)).left ⟶ (baseOver (Sp R)).left := spMap f
  have hτ : τ ≫ (baseOver (Sp R)).hom = (baseOver (Sp K)).hom ≫ spMap f := by simp [τ]
  obtain ⟨U₀, t₀, i₀, c, h₁, h₂, h₃⟩ := H
  obtain ⟨th', hth'⟩ := exists_secRel hp τ hτ hw x.P.isLB x'.P.isLB th
  choose t ht using fun a => exists_secRel hp τ hτ hw x.P.isLB x'.P.isLB (t₀ a)
  have hx : ∀ a, τ ≫ (pt a).left = (pt' a).left ≫ φ := fun a => (hpt a).symm
  have hn : ∀ a, pt' a ^ (m ^ 2) = 1 := fun a => by
    have hx' : τ ≫ (U₀ a).pt.left = (pt' a).left ≫ φ := by rw [(h₁ a).1.pt_eq]; exact hx a
    obtain ⟨α, hα, -⟩ := exists_genThrough₂ hp τ hτ hw x.P.isLB x'.P.isLB (psi_tr' hp τ hτ (pt' a) _ hx')
      (U₀ a).φ (U₀ a).isGen
    exact pow_eq_one_of_gen x'.P (m ^ 2) (pt' a) α hα
  choose U hU hU' using fun a => symLift_move hp τ hτ hw x.P.isLB x'.P.isLB (hx a) (hn a) (h₁ a).1
  have hρ : PMaps w (fun _ : PUnit => eSec x'.P.A) (fun _ => eSec x.P.A) (fun _ => 1) x'.rig x.rig (spMap f) :=
    (maps_iff _ _ _ _ _ _ _ _ (rigPull_le φ (spMap f) he x.P.L) (fun _ => rfl)).1 hrig
  let o : Sp K := IsLocalRing.closedPoint K
  have ho : ∀ p : Sp K, p = o := fun p => Subsingleton.elim _ _
  obtain ⟨i₁, hi₁⟩ := exists_chart x'.P.isLB (eSec x'.P.A o)
  have hR : ∀ p : Sp R, eSec x.P.A p ∈ x.P.L.U i₀ := fun p => by
    have := h₂ (Set.mem_univ p); simpa using this
  have hj₁ : φ (eSec x'.P.A o) ∈ x.P.L.U i₀ := by
    have : (eSec x'.P.A ≫ φ) o ∈ x.P.L.U i₀ := by rw [he]; simpa using hR (spMap f o)
    simpa using this
  have tanU : ∀ j, ∀ p : Sp (DualNumber K), (x'.v j).left p = eSec x'.P.A o := fun j p => by
    obtain ⟨q, rfl⟩ := surj_fst K p
    have h := x'.basis.1 j
    rw [ho q]
    exact congrArg (fun r => r o) h
  have tanD : ∀ j, ∀ p : Sp (DualNumber R), (x.v j).left p ∈ x.P.L.U i₀ := fun j p => by
    obtain ⟨q, rfl⟩ := surj_fst R p
    have h := x.basis.1 j
    have e : (x.v j).left ((spMap (TrivSqZeroExt.fstHom R R R).toRingHom) q) = eSec x.P.A q :=
      congrArg (fun r => r q) h
    rw [e]; exact hR q
  let W := ((x.P.L.pull φ).div x'.P.L).U (fun _ => i₀, i₁)
  have mW : ∀ p : Sp K, eSec x'.P.A p ∈ W := fun p => by rw [ho p]; exact ⟨mem_pull.2 hj₁, hi₁⟩
  let y' : Fin g → (Sp (DualNumber K) ⟶ (baseOver (Sp K) ⊗ x'.P.A).left) :=
    fun j => epsLift (x'.v (j.cast hg'.symm))
  let u₁ : Fin g → DualNumber K :=
    fun j => valR (y' j ≫ (snd (baseOver (Sp K)) x'.P.A).left) W (w.s (fun _ => i₀, i₁)).val
  let u₀ : K := valR (𝟙 (Sp K) ≫ eSec x'.P.A) W (w.s (fun _ => i₀, i₁)).val
  let c' : Fin g → K := fun j => f (c j) - ((m ^ 2 : ℕ) : K) * ((u₁ j).snd / u₀)
  refine ⟨th', polAVSectionInverseImage_chartwisePullback hp τ hτ (gs_theta w x.th x'.th hθ) hth' hth, U, t, i₁, c',
    fun a => ⟨hU a, tr_move_gen hp τ hτ hw he hρ hth' (ht a) (hU' a) (h₁ a).2⟩, ?_, fun a j => ?_⟩
  · intro p _
    rw [ho p]
    exact hi₁
  · let j' : Fin x'.P.g := j.cast hg'.symm
    let j₀ : Fin x.P.g := j.cast hg.symm
    have hvj : (x'.v j').left ≫ φ = spMap F ≫ (x.v j₀).left := by
      have e : j'.cast hgg = j₀ := Fin.ext rfl
      have := hv j'
      rw [e] at this
      exact this
    have ys : y' j ≫ (snd (baseOver (Sp K)) x'.P.A).left = (x'.v j').left := by
      show epsLift _ ≫ _ = _
      rw [epsLift, ← Over.comp_left, lift_snd]
    have yf : y' j ≫ (fst (baseOver (Sp K)) x'.P.A).left = spMap (algebraMap K (DualNumber K)) := by
      show epsLift _ ≫ _ = _
      rw [epsLift, ← Over.comp_left, lift_fst]
      rfl
    have ys₀ : epsLift (x.v j₀) ≫ (snd (baseOver (Sp R)) x.P.A).left = (x.v j₀).left := by
      rw [epsLift, ← Over.comp_left, lift_snd]
    have yf₀ : epsLift (x.v j₀) ≫ (fst (baseOver (Sp R)) x.P.A).left = spMap (algebraMap R (DualNumber R)) := by
      rw [epsLift, ← Over.comp_left, lift_fst]
      rfl
    have hy : y' j ≫ psi hp τ hτ = spMap F ≫ epsLift (x.v j₀) := by
      refine psi_ext ?_ ?_
      · rw [Category.assoc, psi_fst', ← Category.assoc, yf, Category.assoc, yf₀]
        show spMap _ ≫ spMap f = _
        rw [spMap_comp_gen, spMap_comp_gen]
        congr 1
        exact RingHom.ext fun a => (hF1 a).symm
      · rw [Category.assoc, psi_snd', ← Category.assoc, ys, hvj, Category.assoc, ys₀]
    have hFl : ∀ b, F (inl b) = inl (f b) := fun b => (map_inl_inr f F hF1 hF2 b 0).1
    have hFr : ∀ b, F (inr b) = inr (f b) := fun b => (map_inl_inr f F hF1 hF2 0 b).2
    have q := h₃ a j
    have top₀ : ⊤ ≤ (epsLift (x.v j₀)) ⁻¹ᵁ
        ((LPow x.P.A x.P.L ((m ^ 2 : ℕ) : ℤ) (Over.mk (𝟙 (Sp R)))).U fun _ => i₀) :=
      fun p _ => Set.mem_iInter.2 fun _ => by
        show (epsLift (x.v j₀) ≫ (snd (baseOver (Sp R)) x.P.A).left) p ∈ x.P.L.U i₀
        rw [ys₀]
        exact tanD j₀ p
    have qF := congrArg F q
    rw [← valR_spMap_comp' F _ _ top₀, ← hy] at qF
    have hiy : (y' j ≫ (snd (baseOver (Sp K)) x'.P.A).left) (IsLocalRing.closedPoint (DualNumber K)) ∈ x'.P.L.U i₁ := by
      rw [ys]; exact (congrArg (· ∈ x'.P.L.U i₁) (tanU j' _)).mpr hi₁
    have hjy : φ ((y' j ≫ (snd (baseOver (Sp K)) x'.P.A).left) (IsLocalRing.closedPoint (DualNumber K))) ∈ x.P.L.U i₀ := by
      rw [ys]; exact (congrArg (fun p => φ p ∈ x.P.L.U i₀) (tanU j' _)).mpr hj₁
    rw [valR_secRel hp τ hτ x.P.isLB x'.P.isLB (ht a) (y' j) i₀ i₁ hjy hiy] at qF
    rw [map_mul, map_add, hFl, hFl, hFr, map_pow, map_add, map_mul] at qF

    have topρ : ⊤ ≤ (𝟙 (Sp R)) ⁻¹ᵁ ((x.P.L.pull (eSec x.P.A)).U fun _ => i₀) :=
      fun p _ => mem_pull.2 (hR p)
    have hr := valR_rigRel he hρ (𝟙 (Sp K)) i₀ i₁ hj₁ hi₁
    rw [Category.id_comp, ← Category.comp_id (spMap f), valR_spMap_comp' f _ _ topρ] at hr
    rw [hr] at qF

    have topW : ⊤ ≤ (y' j ≫ (snd (baseOver (Sp K)) x'.P.A).left) ⁻¹ᵁ W := fun p _ => by
      show (y' j ≫ (snd (baseOver (Sp K)) x'.P.A).left) p ∈ W
      rw [ys]
      exact (congrArg (· ∈ W) (tanU j' _)).mpr (mW o)
    have hu : (u₁ j).fst = u₀ := by
      have e := valR_spMap_comp' (TrivSqZeroExt.fstHom K K K).toRingHom _ W topW (w.s (fun _ => i₀, i₁)).val
      show (TrivSqZeroExt.fstHom K K K).toRingHom (valR (y' j ≫ _) W _) = valR (𝟙 (Sp K) ≫ eSec x'.P.A) W _
      rw [← e, ys, x'.basis.1 j', Category.id_comp]
      rfl
    have h0 : u₀ ≠ 0 := by
      have m₀ : (𝟙 (Sp K) ≫ eSec x'.P.A) (IsLocalRing.closedPoint K) ∈ W := mW o
      have : IsUnit u₀ := by
        show IsUnit (valR _ W _)
        rw [GlobalTheory.ZH.ThetaData.valR_eq_gs _ _ m₀, gs_unit _ _ _ m₀]
        exact (Units.isUnit _).map _
      exact this.ne_zero
    have key := dual_solve (m ^ 2) (u₁ j) _ u₀ _ (f (ϑ a)) (f (J a j) + f (c j) * f (ϑ a)) hu h0 qF
    rw [key]
    congr 3
    simp only [c']
    push_cast
    ring
