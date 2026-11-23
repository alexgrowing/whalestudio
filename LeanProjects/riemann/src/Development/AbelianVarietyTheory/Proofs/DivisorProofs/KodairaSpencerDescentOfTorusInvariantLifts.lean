import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LeISupInfPreimage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInvariantHeatOperatorPreservesWeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniquePullbackOfRaynaudTorusWeightZeroStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatDescend

open GlobalTheory.KS

theorem alg_sum {Γ₀ R : Type} [CommRing Γ₀] [CommRing R] {g n : ℕ} (κ : R →+* Γ₀) (P : Matrix (Fin g) (Fin n) R)
    (C : Matrix (Fin n) (Fin n) R) (X Z : Fin g → Γ₀) :
    ∑ a, ∑ b, κ (C a b) * (∑ c', κ (P c' b) * X c') * ∑ c, κ (P c a) * Z c =
      ∑ c, ∑ c', κ ((P * C * Pᵀ) c c') * X c' * Z c := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  calc ∑ a, ∑ b, ∑ c, ∑ c', κ (C a b) * (κ (P c' b) * X c') * (κ (P c a) * Z c)
      = ∑ b, ∑ a, ∑ c, ∑ c', κ (C a b) * (κ (P c' b) * X c') * (κ (P c a) * Z c) := Finset.sum_comm
    _ = ∑ b, ∑ c, ∑ c', ∑ a, κ (C a b) * (κ (P c' b) * X c') * (κ (P c a) * Z c) :=
        Finset.sum_congr rfl fun b _ => Finset.sum_comm.trans (Finset.sum_congr rfl fun c _ => Finset.sum_comm)
    _ = ∑ c, ∑ c', ∑ b, ∑ a, κ (C a b) * (κ (P c' b) * X c') * (κ (P c a) * Z c) :=
        Finset.sum_comm.trans (Finset.sum_congr rfl fun c _ => Finset.sum_comm)
    _ = _ := by
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c' _ => Finset.sum_congr rfl fun b _ =>
          Finset.sum_congr rfl fun a _ => ?_
        ring

theorem pbT_id' {X : Scheme.{0}} {U : X.Opens} (s : Γ(X, U)) {O : X.Opens} (h : O ≤ U) : pbT (𝟙 X) s O = rsT s O := by
  rw [pbT_of_le (𝟙 X) (show O ≤ (𝟙 X) ⁻¹ᵁ U from h), rsT_of_le h]
  rfl

theorem valR_pbT {A : Type} [CommRing A] {X Z : Scheme.{0}} (x : Sp A ⟶ Z) (q : Z ⟶ X) (V : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ (q ⁻¹ᵁ V)) (f : Γ(X, V)) :
    valR x (q ⁻¹ᵁ V) (pbT q f (q ⁻¹ᵁ V)) = valR (x ≫ q) V f := by
  rw [GlobalTheory.Heat.WtAlg.valR_eq' x _ h, GlobalTheory.KS.pbT_of_le q le_rfl, GlobalTheory.Heat.WtAlg.valR_eq' (x ≫ q) V h]
  rw [← Scheme.Hom.appLE_comp_appLE x q V (q ⁻¹ᵁ V) ⊤ le_rfl h]
  rfl

theorem isWt_pbT {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
    {oa : Q.OAct O} (Y : Ray oa) (V : Q.P.A.left.Opens) (f : Γ(Q.P.A.left, V)) :
    IsWt Y 0 _ (pbT Y.q.left f (Y.q.left ⁻¹ᵁ V)) := by
  intro S _ φ x x' c a a' ha ha' hV hV' hq hc
  rw [GlobalTheory.Heat.WtAlg.c_zero x x' c hc, Units.val_one, _root_.one_mul, valR_pbT _ _ _ hV', valR_pbT _ _ _ hV]
  subst ha ha'
  have e : x'.left ≫ Y.q.left = x.left ≫ Y.q.left := by
    rw [← Over.comp_left, ← Over.comp_left, hq]
  rw [e]

section General

variable {R : Type} [CommRing R] {G B : Over (Sp R)} (q : G ⟶ B)

theorem exists_lift (hinj : ∀ (O : B.left.Opens) (f f' : Γ(B.left, O)),
      pbT q.left f (q.left ⁻¹ᵁ O) = pbT q.left f' (q.left ⁻¹ᵁ O) → f = f')
    (D : R → R) (V : B.left.Opens) (d : Fld G.left) (hd : IsLift G D (q.left ⁻¹ᵁ V) d)
    (hdesc : ∀ O, O ≤ V → ∀ f : Γ(B.left, O), ∃ f' : Γ(B.left, O),
      pbT q.left f' (q.left ⁻¹ᵁ O) = d _ (pbT q.left f (q.left ⁻¹ᵁ O))) :
    ∃ dB : Fld B.left, IsLift B D V dB ∧ ∀ O, O ≤ V → ∀ f : Γ(B.left, O),
      pbT q.left (dB O f) (q.left ⁻¹ᵁ O) = d _ (pbT q.left f (q.left ⁻¹ᵁ O)) := by
  classical
  have hq : q.left ≫ B.hom = G.hom := Over.w q
  let dB : Fld B.left := fun O f => if h : O ≤ V then (hdesc O h f).choose else 0
  have hB : ∀ O, O ≤ V → ∀ f : Γ(B.left, O),
      pbT q.left (dB O f) (q.left ⁻¹ᵁ O) = d _ (pbT q.left f (q.left ⁻¹ᵁ O)) := by
    intro O h f
    simp only [dB, dif_pos h]
    exact (hdesc O h f).choose_spec
  obtain ⟨⟨h1, h2, h3⟩, h4⟩ := hd
  refine ⟨dB, ⟨⟨fun O h f f' => hinj O _ _ ?_, fun O h f f' => hinj O _ _ ?_, fun O O' h' h f => hinj O' _ _ ?_⟩,
    fun O h r => hinj O _ _ ?_⟩, hB⟩
  · rw [pbT_add, hB O h, hB O h, hB O h, pbT_add, h1 _ (q.left.preimage_mono h)]
  · rw [pbT_add, pbT_mul, pbT_mul, hB O h, hB O h, hB O h, pbT_mul, h2 _ (q.left.preimage_mono h)]
  · have hp : q.left ⁻¹ᵁ O' ≤ q.left ⁻¹ᵁ O := q.left.preimage_mono h'
    rw [hB O' (h'.trans h), ← rsT_of_le h', ← rsT_of_le h', pbT_rsT _ h' le_rfl, pbT_rsT _ h' le_rfl,
      ← rsT_pbT q.left le_rfl hp, ← rsT_pbT q.left le_rfl hp (dB O f), hB O h, rsT_of_le hp, rsT_of_le hp]
    exact h3 _ _ hp (q.left.preimage_mono h) _
  · rw [hB O h, pbT_constFn _ _ le_rfl, pbT_constFn _ _ le_rfl, hq, h4 _ (q.left.preimage_mono h)]

theorem dlg_pull {g : ℕ} (L : LB B.left) (δ : Fld G.left) (e : Fin g → Fld B.left) (he : ∀ c, IsField ⊤ (e c))
    (p : Fin g → R) (hδ : ∀ (V : B.left.Opens) (W : G.left.Opens), W ≤ q.left ⁻¹ᵁ V → ∀ f : Γ(B.left, V),
      δ W (pbT q.left f W) = ∑ c, constFn G.hom W (p c) * pbT q.left (e c V f) W)
    (i i' : L.ι) (O : B.left.Opens) (h : O ≤ L.U i ⊓ L.U i') :
    dlg G q.left L δ i i' (q.left ⁻¹ᵁ O) =
      ∑ c, constFn G.hom _ (p c) * pbT q.left (dlg B (𝟙 _) L (e c) i i' O) (q.left ⁻¹ᵁ O) := by
  unfold dlg
  rw [← pbT_rsT q.left h le_rfl, hδ O _ le_rfl, Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [pbT_mul, pbT_id' _ h, pbT_id' _ h, pbT_rsT q.left h le_rfl, _root_.mul_assoc]

end General

theorem ksRel_of_invLifts : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (g : ℕ) (w : Module.Basis (Fin g) R (TanM (𝟙 (Sp R)) Dd.toPre.P.A)) (e : Fin g → Fld Dd.toPre.P.A.left) (P : Matrix (Fin g) (Fin n) R), (∀ c, IsInv Dd.toPre.P.A (w c) (e c)) → (∀ b (V : Dd.toPre.P.A.left.Opens) (W : Y.H.left.Opens), W ≤ Y.q.left ⁻¹ᵁ V → ∀ f : Γ(Dd.toPre.P.A.left, V), dd b W (pbT Y.q.left f W) = ∑ c, constFn Y.H.hom W (P c b) * pbT Y.q.left (e c V f) W) → ∀ (D : Derivation ℤ R R) (J : Type) (V : J → Dd.toPre.P.A.left.Opens) (j : J → Dd.toPre.P.L.ι) (d : J → Fld Y.H.left), ⨆ i, V i = ⊤ → (∀ i, V i ≤ Dd.toPre.P.L.U (j i)) → (∀ i, IsLift Y.H ⇑D (Y.q.left ⁻¹ᵁ V i) (d i)) → (∀ i, (∀ (α : Dd.toPre.X) (V' : Dd.toPre.P.A.left.Opens), Y.q.left ⁻¹ᵁ V' ≤ Y.q.left ⁻¹ᵁ V i → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V') f → IsWt Y α (Y.q.left ⁻¹ᵁ V') (d i _ f))) → ∀ C : Matrix (Fin n) (Fin n) R, (∀ i i' (W : Y.H.left.Opens), W ≤ Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i' → ∀ f, d i W f - d i' W f = ∑ a, ∑ b, constFn Y.H.hom W (C a b) * dlg Y.H Y.q.left Dd.toPre.P.L (dd b) (j i) (j i') W * dd a W f) → KSRel Dd.toPre.P.A (𝟙 Dd.toPre.P.A.left) Dd.toPre.P.L e ⇑D (P * C * Pᵀ) := by
  intro R _ _ _ _ _ _ Dd O _ _ _ oa Y n v dd _ g w e P he hP D J V j d hcov hle hlift hwt C hC
  have hA := GlobalTheory.T.existsUnique_pullback_of_raynaudTorusWeight_zero R Dd.toPre O oa Y
  have hinj : ∀ (U : Dd.toPre.P.A.left.Opens) (f f' : Γ(Dd.toPre.P.A.left, U)),
      pbT Y.q.left f (Y.q.left ⁻¹ᵁ U) = pbT Y.q.left f' (Y.q.left ⁻¹ᵁ U) → f = f' := fun U f f' h =>
    (hA U _ (isWt_pbT Y U f')).unique h rfl
  choose dB hB hB' using fun i => exists_lift Y.q hinj D (V i) (d i) (hlift i) fun U hU f =>
    (hA U _ (hwt i 0 U (Y.q.left.preimage_mono hU) _ (isWt_pbT Y U f))).exists
  refine ⟨J, V, j, dB, hcov, hle, hB, fun i i' U hU f => hinj U _ _ ?_⟩
  have hq : Y.q.left ≫ Dd.toPre.P.A.hom = Y.H.hom := Over.w Y.q
  have hL : U ≤ Dd.toPre.P.L.U (j i) ⊓ Dd.toPre.P.L.U (j i') := hU.trans (inf_le_inf (hle i) (hle i'))
  rw [pbT_sub, hB' i U (hU.trans inf_le_left), hB' i' U (hU.trans inf_le_right),
    hC i i' _ (Y.q.left.preimage_mono hU)]
  simp only [fun b => dlg_pull Y.q Dd.toPre.P.L (dd b) e (fun c => (he c).1) (fun c => P c b) (hP b) _ _ U hL,
    fun a => hP a U _ le_rfl f, pbT_sum, pbT_mul, pbT_constFn _ Y.q.left (O₀ := U) le_rfl, hq]
  exact alg_sum ((Y.H.hom.appLE ⊤ _ (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) P C _ _

end GlobalTheory.HeatDescend
