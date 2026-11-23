import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.RosatiAdj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Theta1
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.ExistsGeneratorOfIsField

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

def levelBasis {S : Scheme.{0}} {P : PolAV S} {M : ℕ} {ze : Γ(S, ⊤)ˣ} (lev : Level P M ze) {g : ℕ}
    (hg : P.g = g) (i : Fin (2 * g)) : baseOver S ⟶ P.A :=
  lev.pt (Fin.cast (congrArg (2 * ·) hg.symm) i)

def levelPoint {S : Scheme.{0}} {P : PolAV S} {M : ℕ} {ze : Γ(S, ⊤)ˣ} (lev : Level P M ze) {g : ℕ}
    (hg : P.g = g) (a : Fin (2 * g) → ZMod M) : baseOver S ⟶ P.A :=
  lev.toPt fun i => a (Fin.cast (congrArg (2 * ·) hg) i)

theorem levelBasis_rfl {S : Scheme.{0}} {P : PolAV S} {M : ℕ} {ze : Γ(S, ⊤)ˣ} (lev : Level P M ze) :
    levelBasis lev rfl = lev.pt := rfl

theorem levelPoint_rfl {S : Scheme.{0}} {P : PolAV S} {M : ℕ} {ze : Γ(S, ⊤)ˣ} (lev : Level P M ze) :
    levelPoint lev rfl = lev.toPt := rfl

def IsPolIso {S : Scheme.{0}} (P P' : PolAV S) (φ : P.A ≅ P'.A) : Prop :=
  IsMonHom φ.hom ∧ ∃ t : LB.Iso (P'.L.pull φ.hom.left) P.L, t.IsGen

def ThetaPtDeterminesSt : Prop :=
  ∀ (g n k j N N' : ℕ), n.Prime → Odd n → 2 ≤ k → N = (n ^ k) ^ 2 → N' = n ^ j * N →
    N ^ g * g.factorial < N' →
    ∀ (K : Type) [Field K] [IsAlgClosed K], (n : K) ≠ 0 →
    ∀ (P P' : PolAV (Spec (CommRingCat.of K))) (hg : P.g = g) (hg' : P'.g = g)
      (ze : Γ(Spec (CommRingCat.of K), ⊤)ˣ) (lev : Level P (N' ^ 2) ze) (lev' : Level P' (N' ^ 2) ze)
      (v : (Fin (2 * g) → ZMod (N' ^ 2)) → Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤)),
      IsThetaPt P N' (levelPoint lev hg) v → IsThetaPt P' N' (levelPoint lev' hg') v →
      ∃ φ : P.A ≅ P'.A, IsPolIso P P' φ ∧ ∀ i, levelBasis lev hg i ≫ φ.hom = levelBasis lev' hg' i

def StarNormLE {O : Type} [Ring O] [StarRing O] (a : O) (c : ℕ) : Prop :=
  ∃ (m r : ℕ) (b : Fin r → O), 1 ≤ m ∧
    star ((m : O) * a) * ((m : O) * a) + ∑ i, star (b i) * b i = (c : O)

def EndDeterminedOnTorsionSt : Prop :=
  ∀ (g c M : ℕ), 4 ^ g * g.factorial * (2 * c) < M ^ 2 →
    ∀ (K : Type) [Field K] [IsAlgClosed K], (M : K) ≠ 0 →
    ∀ (P P' : PolAV (Spec (CommRingCat.of K))), P.g = g → P'.g = g →
    ∀ (φ : P.A ≅ P'.A), IsPolIso P P' φ →
    ∀ (O : Type) [Ring O] [StarRing O] (ρ : P.OAct O) (ρ' : P'.OAct O) (a : O), StarNormLE a c →
      (∀ x : baseOver (Spec (CommRingCat.of K)) ⟶ P.A, x ^ M = 1 →
        x ≫ ρ.act a ≫ φ.hom = x ≫ φ.hom ≫ ρ'.act a) →
      ρ.act a ≫ φ.hom = φ.hom ≫ ρ'.act a

namespace ThetaPtDet

open scoped CategoryTheory.Obj

theorem linComb_comp {S : Scheme.{0}} {A B T : Over S} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f] {r : ℕ}
    (y : Fin r → (T ⟶ A)) (a : Fin r → ℕ) : linComb y a ≫ f = linComb (fun i => y i ≫ f) a := by
  let F : (T ⟶ A) →* (T ⟶ B) := IsMonHom.monoidHom f T
  have h := map_list_prod F (List.ofFn fun i => y i ^ a i)
  rw [List.map_ofFn] at h
  refine h.trans (congrArg List.prod (congrArg List.ofFn (funext fun i => ?_)))
  exact map_pow F (y i) (a i)

theorem levelPoint_eq {S : Scheme.{0}} {P : PolAV S} {M : ℕ} {ze : Γ(S, ⊤)ˣ} (lev : Level P M ze) {g : ℕ}
    (hg : P.g = g) (a : Fin (2 * g) → ZMod M) :
    levelPoint lev hg a = linComb (levelBasis lev hg) (fun i => (a i).val) := by
  subst hg; rfl

section One

variable {X Y Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K'] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
  {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')}

theorem corr_of_one (h : ∀ j, t.s j = 1) (h' : ∀ j, t'.s j = 1) : LB.Gen.Corr L φ ε φ' ε' t t' :=
  fun j j' _ _ _ => by erw [h, h']; exact (map_one _).trans (map_one _).symm

theorem one_pullGen (h : ∀ j, t.s j = 1) (f : Z ⟶ Y) (j) : (LB.pullGen L φ ε t f).s j = 1 := by
  dsimp only [LB.pullGen]
  erw [h]
  exact (congrArg _ (map_one _)).trans (map_one _)

theorem one_mulGen (h : ∀ j, t.s j = 1) (h' : ∀ j, t'.s j = 1) (j) : (LB.mulGen L φ ε φ' ε' t t').s j = 1 := by
  dsimp only [LB.mulGen]
  erw [h, h']
  exact (congrArg₂ (· * ·) (map_one _) (map_one _)).trans (_root_.mul_one _)

theorem one_invGen (h : ∀ j, t.s j = 1) (j) : (LB.invGen L φ ε t).s j = 1 := by
  dsimp only [LB.invGen]
  erw [h]
  exact inv_one

theorem one_powGen {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ} {T : Over S}
    (θ : ThetaGrp A L k T) (n : ℕ) (h : ∀ j, θ.φ.s j = 1) (j) : (powGen A L k θ n).s j = 1 := by
  dsimp only [powGen]
  refine Finset.prod_eq_one fun i _ => ?_
  exact (congrArg _ (one_pullGen (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) h _ _)).trans
    (map_one _)

end One

section Zero

open Inh InhVV

variable (S : Scheme.{0})

def zeroLevel (M : ℕ) (ze : Γ(S, ⊤)ˣ) (h : IsPrimitiveRoot ze M) : Level (zeroPolAV S) M ze where
  pt := fun i => Fin.elim0 i
  prim := h
  torsion := fun i => Fin.elim0 i
  indep := fun _ _ _ _ _ _ _ => funext fun i => Fin.elim0 i
  span := fun _ _ _ _ _ _ => ⟨fun i => Fin.elim0 i, toUnit_unique _ _⟩
  pairing := fun i => Fin.elim0 i

theorem isThetaPt_zero (k : ℕ) (hk : Odd k) {T : Over S} (hu : IsUnit (k : Γ(T.left, ⊤))) {I : Type}
    (x : I → (T ⟶ (zeroPolAV S).A)) : IsThetaPt (zeroPolAV S) k x (fun _ => 1) := by
  refine ⟨hk, hu, fun p => ⟨⊤, trivial, oneSec S 1 _, oneSec S _ _, ⟨fun _ => 1⟩, ⟨fun _ => 1⟩,
    fun _ => theta1 S _ _, fun _ => oneSec S _ _, fun _ => 1, 1, ?_, ?_, ?_, ?_, fun i => ⟨?_, ?_, ?_⟩,
    ?_, ?_, ?_⟩⟩
  · intro s
    haveI : IsIso (fst (overRes (T := T) ⊤) (zeroPolAV S).A) := by
      show IsIso (fst _ (𝟙_ (Over S)))
      rw [← rightUnitor_hom]; infer_instance
    haveI : IsIso (fst (overRes (T := T) ⊤) (zeroPolAV S).A).left :=
      inferInstanceAs (IsIso ((Over.forget S).map (fst (overRes (T := T) ⊤) (zeroPolAV S).A)))
    obtain ⟨r, hr⟩ := surj_appLE (fst (overRes (T := T) ⊤) (zeroPolAV S).A).left
      ((LPow (zeroPolAV S).A (zeroPolAV S).L 1 (overRes (T := T) ⊤)).U fun _ => PUnit.unit)
      (top_unique fun y _ => Set.mem_iInter.2 fun _ => trivial) le_top (s.f fun _ => PUnit.unit)
    exact ⟨r, fun j => hr.symm.trans (_root_.mul_one _).symm⟩
  · intro i j
    erw [linComb_triv_g, _root_.one_mul]; repeat erw [map_one]
  · intro i j
    erw [linComb_triv_g, _root_.one_mul]; repeat erw [map_one]
  · intro j
    simp only [oneSec, Units.val_one]
    (repeat erw [map_one]); (try erw [_root_.one_mul])
  · exact toUnit_unique _ _
  · intro j j' _ _ _
    exact corr_of_one (one_powGen _ _ fun _ => rfl) (fun _ => rfl) j j' ‹_› ‹_› ‹_›
  · refine ⟨⟨fun _ => 1⟩, ?_, ?_⟩
    · intro i j
      erw [linComb_triv_g, _root_.one_mul]; repeat erw [map_one]
    · intro j j' _ _ _
      exact corr_of_one (one_mulGen (one_mulGen (one_pullGen (fun _ => rfl) _) fun _ => rfl)
        (one_mulGen (one_pullGen (fun _ => rfl) _) (one_invGen (one_pullGen (fun _ => rfl) _))))
        (fun _ => rfl) j j' ‹_› ‹_› ‹_›
  · intro i j
    refine (map_one _).trans (Eq.symm ?_)
    exact (_root_.one_mul _).trans ((congrArg _ (map_one _)).trans (map_one _))
  · intro i j
    exact ((congrArg _ (map_one _)).trans (map_one _)).trans
      ((_root_.mul_one _).trans ((congrArg _ rfl).trans (map_one _))).symm
  · intro i
    simp

end Zero

section AnyDimension

theorem levelPoint_pow {S : Scheme.{0}} {P : PolAV S} {M : ℕ} {ze : Γ(S, ⊤)ˣ} (lev : Level P M ze) {g : ℕ}
    (hg : P.g = g) (a : Fin (2 * g) → ZMod M) : levelPoint lev hg a ^ M = 1 := by
  subst hg
  have := P.isAb.comm
  have cm : ∀ x y : baseOver S ⟶ P.A, Commute x y := fun x y => _root_.mul_comm x y
  refine List.prod_induction (fun y => y ^ M = 1) (fun x y hx hy => ?_) (one_pow _) fun y hy => ?_
  · rw [(cm x y).mul_pow, hx, hy, _root_.mul_one]
  · obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hy
    rw [← pow_mul, Nat.mul_comm, pow_mul, lev.torsion, one_pow]

theorem exists_thetaPt_of_level (hLaw : Laws) (K : Type) [Field K] [IsAlgClosed K]
    (P : PolAV (Spec (CommRingCat.of K))) {g : ℕ} (hg : P.g = g) (N' : ℕ) (ho : Odd N') (hK : (N' : K) ≠ 0)
    {ze : Γ(Spec (CommRingCat.of K), ⊤)ˣ} (lev : Level P (N' ^ 2) ze) :
    ∃ v, IsThetaPt P N' (levelPoint lev hg) v :=
  ThetaPtExist.exists_isThetaPt hLaw K P N' ho hK _ (levelPoint_pow lev hg)

theorem isPolIso_refl {S : Scheme.{0}} (P : PolAV S) : IsPolIso P P (Iso.refl _) :=
  ⟨inferInstanceAs (IsMonHom (𝟙 _)), Geo.Tor.LBIso.chartPull (Geo.Tor.chartPullPull P.L _ (𝟙 _) rfl)
    (Geo.Tor.chartPullId _) (PolBaseChange.lbIso_refl P.isLB)⟩

theorem act_natCast {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {O : Type} [Ring O]
    (ρ : RingAct A O) (m : ℕ) : ρ.act (m : O) = 𝟙 A ^ m := by
  have add : ∀ a b, ρ.act (a + b) = ρ.act a * ρ.act b := ρ.map_add
  induction m with
  | zero =>
    have h := add 0 0
    rw [add_zero] at h
    rw [Nat.cast_zero, pow_zero]
    exact left_eq_mul.1 h
  | succ m ih => rw [Nat.cast_succ, add, ih, ρ.map_one, pow_succ]

theorem conclusion_natCast {S : Scheme.{0}} (P P' : PolAV S) (φ : P.A ≅ P'.A) (hφ : IsPolIso P P' φ)
    {O : Type} [Ring O] [StarRing O] (ρ : P.OAct O) (ρ' : P'.OAct O) (m : ℕ) :
    ρ.act (m : O) ≫ φ.hom = φ.hom ≫ ρ'.act (m : O) := by
  have := hφ.1
  rw [act_natCast ρ.toRingAct, act_natCast ρ'.toRingAct, MonObj.comp_pow, Category.comp_id]
  exact (map_pow (IsMonHom.monoidHom φ.hom P.A) _ m).trans (congrArg (· ^ m) (Category.id_comp φ.hom))

end AnyDimension

end ThetaPtDet

end GlobalTheory
