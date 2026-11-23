import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusInvariantHeatOperatorOfSymmetricRelat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInvariantLiftAddInvariantCombination
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInvariantLiftsSubEqSumInvariantFieldsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudExtensionInvariantFieldCoeffsUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudWeightZeroCompatibleFunctionsEqBaseConstaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantFieldCombKillsWeightZeroOfCoboundaryStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
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

namespace GlobalTheory.HeatUniqGlob

open GlobalTheory.HeatGlue GlobalTheory.KS

theorem sep {Γ : Type} [CommRing Γ] {c x y : Γ} (hc : 2 * c = 1) (h : ∀ k : ℕ, (k : Γ) * x + (k : Γ) ^ 2 * y = 0) :
    x = 0 ∧ y = 0 := by
  have h1 := h 1
  have h2 := h 2
  push_cast at h1 h2
  have hy : y = 0 := by linear_combination (-c) * (2 * h1 - h2) - y * hc
  exact ⟨by linear_combination h1 - hy, hy⟩

theorem within {R : Type} [CommRing R] [Algebra ℚ R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    {X : Scheme.{0}} {m : G.left ⟶ X} {L : LB X} {n : ℕ} {dd : Fin n → Fld G.left} {D : R → R}
    (hdd : ∀ a, IsField ⊤ (dd a)) (h : Heat G m L dd D) (i i' : h.J) (Wo : G.left.Opens)
    (hW : Wo ≤ h.W i ⊓ h.W i') :
    (∀ f, h.d i Wo f - h.d i' Wo f =
      ∑ a, ∑ b, constFn G.hom Wo (h.Θ a b) * dlg G m L (dd b) (h.j i) (h.j i') Wo * dd a Wo f) ∧
    2 * (rsT (h.p i) Wo - rsT (h.p i') Wo) + 2 * dlg G m L (h.d i) (h.j i) (h.j i') Wo -
      ∑ a, ∑ b, constFn G.hom Wo (h.Θ a b) * dlg G m L (dd a) (h.j i) (h.j i') Wo *
        dlg G m L (dd b) (h.j i) (h.j i') Wo = 0 ∧
    2 * (rsT (h.p' i) Wo - rsT (h.p' i') Wo) +
      2 * ∑ a, constFn G.hom Wo (h.u a) * dlg G m L (dd a) (h.j i) (h.j i') Wo -
      ∑ a, ∑ b, constFn G.hom Wo (h.Θ a b) * dd a Wo (dlg G m L (dd b) (h.j i) (h.j i') Wo) = 0 := by
  have hm : Wo ≤ m ⁻¹ᵁ (L.U (h.j i) ⊓ L.U (h.j i')) :=
    le_inf (hW.trans (inf_le_left.trans (h.le i))) (hW.trans (inf_le_right.trans (h.le i')))
  have hg := pbT_unit' m (L.g (h.j i) (h.j i')) hm
  have hdi : IsDer (h.d i Wo) := isDer_of_isField (h.lift i).1 (hW.trans inf_le_left)
  have hdi' : IsDer (h.d i' Wo) := isDer_of_isField (h.lift i').1 (hW.trans inf_le_right)
  have hdd' : ∀ a, IsDer (dd a Wo) := fun a => isDer_of_isField (hdd a) le_top
  have hs : ∀ a b, (h.Θ.map (constFn G.hom Wo)) a b = (h.Θ.map (constFn G.hom Wo)) b a := fun a b => by
    simp only [Matrix.map_apply]; rw [show h.Θ a b = h.Θᵀ b a from rfl, h.symm]
  have h2 : (2 : R) * algebraMap ℚ R (1 / 2) = 1 := by
    rw [← map_ofNat (algebraMap ℚ R) 2, ← map_mul]; norm_num
  have two : (2 : Γ(G.left, Wo)) * constFn G.hom Wo (algebraMap ℚ R (1 / 2)) = 1 := by
    rw [← constFn_two G.hom Wo, ← constFn_mul, h2, constFn_one]
  unfold dlg
  set g := pbT m (L.g (h.j i) (h.j i')).val Wo with hgdef
  set gi := pbT m (L.g (h.j i) (h.j i'))⁻¹.val Wo with hgidef
  have gk : ∀ k : ℕ, gi ^ k * g ^ k = 1 := fun k => by rw [← mul_pow, mul_comm, hg, one_pow]
  have key : ∀ f, (∀ k : ℕ, (k : Γ(G.left, Wo)) *
        (2 * (h.d i Wo f - h.d i' Wo f - ∑ a, ∑ b, constFn G.hom Wo (h.Θ a b) * (dd b Wo g * gi) * dd a Wo f) +
          (2 * (rsT (h.p' i) Wo - rsT (h.p' i') Wo) + (2 * ∑ a, constFn G.hom Wo (h.u a) * (dd a Wo g * gi) -
            ∑ a, ∑ b, constFn G.hom Wo (h.Θ a b) * dd a Wo (dd b Wo g * gi))) * f) +
      (k : Γ(G.left, Wo)) ^ 2 * ((2 * (rsT (h.p i) Wo - rsT (h.p i') Wo) + (2 * (h.d i Wo g * gi) -
        ∑ a, ∑ b, constFn G.hom Wo (h.Θ a b) * (dd a Wo g * gi) * (dd b Wo g * gi))) * f) = 0) := by
    intro f k
    have c := ringOp_conj hdi hdd' (Θ := h.Θ.map (constFn G.hom Wo)) hs (fun a => constFn G.hom Wo (h.u a))
      (rsT (h.p i) Wo) (rsT (h.p' i) Wo) hg k f
    have gl := h.glue k i i' Wo hW f
    simp only [op] at gl
    simp only [ringOp, Matrix.map_apply] at c
    rw [c] at gl
    have canc : ∀ z : Γ(G.left, Wo), g ^ k * z = 0 → z = 0 := fun z hz => by
      have e := congrArg (gi ^ k * ·) hz
      simp only [mul_zero] at e
      rw [← _root_.mul_assoc, gk, _root_.one_mul] at e
      exact e
    apply canc
    linear_combination gl
  have hB := fun f => (sep two (key f)).2
  have hX := fun f => (sep two (key f)).1
  have B0 := hB 1
  rw [_root_.mul_one] at B0
  have C0 := hX 1
  rw [hdi.map_one, hdi'.map_one, _root_.mul_one] at C0
  simp only [(hdd' _).map_one, mul_zero, Finset.sum_const_zero, sub_zero] at C0
  refine ⟨fun f => ?_, by linear_combination B0, by linear_combination C0⟩
  have A0 := hX f
  rw [show (2 * (rsT (h.p' i) Wo - rsT (h.p' i') Wo) + (2 * ∑ a, constFn G.hom Wo (h.u a) * (dd a Wo g * gi) -
      ∑ a, ∑ b, constFn G.hom Wo (h.Θ a b) * dd a Wo (dd b Wo g * gi))) = 0 by linear_combination C0] at A0
  linear_combination (constFn G.hom Wo (algebraMap ℚ R (1 / 2))) * A0 -
    (h.d i Wo f - h.d i' Wo f - ∑ a, ∑ b, constFn G.hom Wo (h.Θ a b) * (dd b Wo g * gi) * dd a Wo f) * two

end GlobalTheory.HeatUniqGlob

namespace GlobalTheory.HeatUniqGlob

open GlobalTheory.HeatGlue GlobalTheory.KS

theorem isField_mono {Z : Scheme.{0}} {W W' : Z.Opens} {d : Fld Z} (h : IsField W d) (hle : W' ≤ W) : IsField W' d :=
  ⟨fun O hO => h.1 O (hO.trans hle), fun O hO => h.2.1 O (hO.trans hle), fun O O' h' hO => h.2.2 O O' h' (hO.trans hle)⟩

theorem isLift_mono {R : Type} [CommRing R] {G : Over (Sp R)} {D : R → R} {W W' : G.left.Opens} {d : Fld G.left}
    (h : IsLift G D W d) (hle : W' ≤ W) : IsLift G D W' d :=
  ⟨isField_mono h.1 hle, fun O hO r => h.2 O (hO.trans hle) r⟩

theorem rsT_two {Z : Scheme.{0}} {O₀ O : Z.Opens} (h : O ≤ O₀) : rsT (2 : Γ(Z, O₀)) O = 2 := by
  rw [show (2 : Γ(Z, O₀)) = 1 + 1 by norm_num, rsT_add, rsT_one h]; norm_num

end GlobalTheory.HeatUniqGlob

namespace GlobalTheory.HeatUniqGlob

open GlobalTheory.HeatGlue GlobalTheory.KS

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [Algebra ℚ R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (h h' : Heat Y.H Y.q.left Q.P.L dd ⇑D), IsBasic Y h → IsBasic Y h' → h.Θ = h'.Θ → h.u = h'.u → ∃ (e : Fin n → R) (π π' : R), (∀ (V : Q.P.A.left.Opens) f, IsWt Y 0 (Y.q.left ⁻¹ᵁ V) f → ∑ a, constFn Y.H.hom _ (e a) * dd a _ f = 0) ∧ ∀ (i : h.J) (i' : h'.J) (Wo : Y.H.left.Opens), Wo ≤ h.W i ⊓ h'.W i' → (∀ f, h.d i Wo f - h'.d i' Wo f = ∑ a, constFn Y.H.hom Wo (e a) * dd a Wo f + ∑ a, ∑ b, constFn Y.H.hom Wo (h.Θ a b) * dlg Y.H Y.q.left Q.P.L (dd b) (h.j i) (h'.j i') Wo * dd a Wo f) ∧ 2 * (rsT (h.p i) Wo - rsT (h'.p i') Wo) + 2 * dlg Y.H Y.q.left Q.P.L (h.d i) (h.j i) (h'.j i') Wo - ∑ a, ∑ b, constFn Y.H.hom Wo (h.Θ a b) * dlg Y.H Y.q.left Q.P.L (dd a) (h.j i) (h'.j i') Wo * dlg Y.H Y.q.left Q.P.L (dd b) (h.j i) (h'.j i') Wo = 2 * constFn Y.H.hom Wo π ∧ 2 * (rsT (h.p' i) Wo - rsT (h'.p' i') Wo) + 2 * ∑ a, constFn Y.H.hom Wo (h.u a) * dlg Y.H Y.q.left Q.P.L (dd a) (h.j i) (h'.j i') Wo - ∑ a, ∑ b, constFn Y.H.hom Wo (h.Θ a b) * dd a Wo (dlg Y.H Y.q.left Q.P.L (dd b) (h.j i) (h'.j i') Wo) = 2 * constFn Y.H.hom Wo π' := by
  intro R _ _ _ _ _ Q O _ _ _ oa Y n v dd hinv D h h' hB hB' hΘ hu
  have hL : Q.P.L.IsLB := Q.P.isLB
  have hddF : ∀ a, IsField ⊤ (dd a) := fun a => (hinv a).1
  have hdd : ∀ a (W : Y.H.left.Opens), IsDer (dd a W) := fun a W => isDer_of_isField (hddF a) le_top
  have h2 : (2 : R) * algebraMap ℚ R (1 / 2) = 1 := by
    rw [← map_ofNat (algebraMap ℚ R) 2, ← map_mul]; norm_num
  have two : ∀ W : Y.H.left.Opens, (2 : Γ(Y.H.left, W)) * constFn Y.H.hom W (algebraMap ℚ R (1 / 2)) = 1 := fun W => by
    rw [← constFn_two Y.H.hom W, ← constFn_mul, h2, constFn_one]
  have hs : ∀ (W : Y.H.left.Opens) a b, constFn Y.H.hom W (h.Θ a b) = constFn Y.H.hom W (h.Θ b a) := fun W a b => by
    rw [show h.Θ a b = h.Θᵀ b a from rfl, h.symm]
  choose V hV using fun i => (hB i).1
  choose V' hV' using fun i' => (hB' i').1
  have W1 := within hddF h
  have W2 := within hddF h'
  rw [← hΘ, ← hu] at W2
  let K : Type := h.J × h'.J
  let Wk : K → Y.H.left.Opens := fun k => Y.q.left ⁻¹ᵁ (V k.1 ⊓ V' k.2)
  have hWk : ∀ k : K, Wk k = h.W k.1 ⊓ h'.W k.2 := fun k => by rw [hV, hV']; rfl
  have hcov : ⨆ k, Wk k = ⊤ := by
    simp only [hWk]
    rw [← iSup_inf_iSup, h.cover, h'.cover, inf_top_eq]
  have l1 : ∀ k : K, Wk k ≤ h.W k.1 := fun k => (hWk k).le.trans inf_le_left
  have l2 : ∀ k : K, Wk k ≤ h'.W k.2 := fun k => (hWk k).le.trans inf_le_right
  have uh : ∀ {Wo : Y.H.left.Opens} {i : h.J}, Wo ≤ h.W i → Wo ≤ Y.q.left ⁻¹ᵁ Q.P.L.U (h.j i) := fun hw => hw.trans (h.le _)
  have uh' : ∀ {Wo : Y.H.left.Opens} {i : h'.J}, Wo ≤ h'.W i → Wo ≤ Y.q.left ⁻¹ᵁ Q.P.L.U (h'.j i) :=
    fun hw => hw.trans (h'.le _)
  have hWU : ∀ k : K, Wk k ≤ Y.q.left ⁻¹ᵁ (Q.P.L.U (h.j k.1) ⊓ Q.P.L.U (h'.j k.2)) := fun k =>
    le_inf (uh (l1 k)) (uh' (l2 k))

  have ex : ∀ k : K, ∃ c : Fin n → Γ(Y.H.left, Wk k), (∀ a, IsWt Y 0 _ (c a)) ∧ ∀ Wo, Wo ≤ Wk k → ∀ f,
      h.d k.1 Wo f - h'.d k.2 Wo f = ∑ a, rsT (c a) Wo * dd a Wo f := fun k =>
    GlobalTheory.T.torusInvariant_lifts_sub_eq_sum_invariantFields R Q O oa Y n v dd hinv (V k.1 ⊓ V' k.2) D (h.d k.1) (h'.d k.2) (isLift_mono (h.lift _) (l1 k))
      (isLift_mono (h'.lift _) (l2 k))
      (fun α V'' hV'' f hf => (hB k.1).2.2.2 α V'' ((Y.q.left.preimage_mono hV'').trans (l1 k)) f hf)
      (fun α V'' hV'' f hf => (hB' k.2).2.2.2 α V'' ((Y.q.left.preimage_mono hV'').trans (l2 k)) f hf)
  choose c hcw hc using ex
  have wℓ : ∀ (k : K) (δ : Fld Y.H.left), (∀ f, IsWt Y 0 (Wk k) f → IsWt Y 0 (Wk k) (δ (Wk k) f)) →
      IsWt Y 0 (Wk k) (dlg Y.H Y.q.left Q.P.L δ (h.j k.1) (h'.j k.2) (Wk k)) := fun k δ hδ => by
    unfold dlg
    exact isWt_zero_mul (hδ _ (isWt_zero_pbT _ (hWU k))) (isWt_zero_pbT _ (hWU k))
  obtain ⟨E, hE⟩ : ∃ E : ∀ k : K, Fin n → Γ(Y.H.left, Wk k), ∀ k a, E k a = c k a -
      ∑ b, constFn Y.H.hom (Wk k) (h.Θ a b) * dlg Y.H Y.q.left Q.P.L (dd b) (h.j k.1) (h'.j k.2) (Wk k) :=
    ⟨_, fun _ _ => rfl⟩
  have wE : ∀ k a, IsWt Y 0 _ (E k a) := fun k a => by
    rw [hE]
    exact isWt_sub (hcw k a) (isWt_sum _ _ fun b _ => isWt_zero_mul (isWt_zero_constFn _ _)
      (wℓ k (dd b) fun f hf => isWt_inv (hinv b) hf))
  have PE : ∀ (k : K) (Wo : Y.H.left.Opens), Wo ≤ Wk k → ∀ f, h.d k.1 Wo f - h'.d k.2 Wo f =
      ∑ a, rsT (E k a) Wo * dd a Wo f +
        ∑ a, ∑ b, constFn Y.H.hom Wo (h.Θ a b) * dlg Y.H Y.q.left Q.P.L (dd b) (h.j k.1) (h'.j k.2) Wo * dd a Wo f := by
    intro k Wo hWo f
    have e : ∀ b, rsT (dlg Y.H Y.q.left Q.P.L (dd b) (h.j k.1) (h'.j k.2) (Wk k)) Wo =
        dlg Y.H Y.q.left Q.P.L (dd b) (h.j k.1) (h'.j k.2) Wo := fun b =>
      rsT_dlg _ _ _ (hddF b) _ _ le_top hWo (hWU k)
    rw [hc k Wo hWo f]
    simp only [hE, rsT_sub, rsT_sum, rsT_mul, rsT_constFn _ hWo, e, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul]
    ring

  have cE : ∀ (k k' : K) (Wo : Y.H.left.Opens), Wo ≤ Wk k ⊓ Wk k' → ∀ a, rsT (E k a) Wo = rsT (E k' a) Wo := by
    intro k k' Wo hWo
    have hk : Wo ≤ Wk k := hWo.trans inf_le_left
    have hk' : Wo ≤ Wk k' := hWo.trans inf_le_right
    have z := GlobalTheory.T.raynaudExtension_invariantField_coeffs_unique R Q O oa Y n v dd hinv Wo (fun a => rsT (E k a) Wo - rsT (E k' a) Wo) (fun Wo' hWo' f => by
      have h1 : Wo' ≤ Wk k := hWo'.trans hk
      have h2 : Wo' ≤ Wk k' := hWo'.trans hk'
      simp only [rsT_sub, rsT_rsT hk hWo', rsT_rsT hk' hWo', sub_mul, Finset.sum_sub_distrib]
      have p1 := PE k Wo' h1 f
      have p2 := PE k' Wo' h2 f
      have w1 := (W1 k.1 k'.1 Wo' (le_inf (h1.trans (l1 k)) (h2.trans (l1 k')))).1 f
      have w2 := (W2 k.2 k'.2 Wo' (le_inf (h1.trans (l2 k)) (h2.trans (l2 k')))).1 f
      have c1 : ∀ b, dlg Y.H Y.q.left Q.P.L (dd b) (h.j k.1) (h'.j k.2) Wo' =
          dlg Y.H Y.q.left Q.P.L (dd b) (h.j k.1) (h.j k'.1) Wo' + dlg Y.H Y.q.left Q.P.L (dd b) (h.j k'.1) (h'.j k.2) Wo' :=
        fun b => dlg_cocycle Y.H Y.q.left Q.P.L hL _ _ _ (hdd b Wo')
          (le_inf (le_inf (uh (h1.trans (l1 k))) (uh (h2.trans (l1 k')))) (uh' (h1.trans (l2 k))))
      have c2 : ∀ b, dlg Y.H Y.q.left Q.P.L (dd b) (h.j k'.1) (h'.j k'.2) Wo' =
          dlg Y.H Y.q.left Q.P.L (dd b) (h.j k'.1) (h'.j k.2) Wo' + dlg Y.H Y.q.left Q.P.L (dd b) (h'.j k.2) (h'.j k'.2) Wo' :=
        fun b => dlg_cocycle Y.H Y.q.left Q.P.L hL _ _ _ (hdd b Wo')
          (le_inf (le_inf (uh (h2.trans (l1 k'))) (uh' (h1.trans (l2 k)))) (uh' (h2.trans (l2 k'))))
      simp only [c1, c2, add_mul, mul_add, Finset.sum_add_distrib] at p1 p2
      linear_combination -p1 + p2 + w1 - w2)
    exact fun a => sub_eq_zero.1 (z a)
  have ce : ∀ a, ∃ r : R, ∀ k, E k a = constFn Y.H.hom _ r := fun a =>
    GlobalTheory.T.raynaud_weight_zero_compatible_functions_eq_base_constant R Q O oa Y K Wk (fun k => ⟨_, rfl⟩) hcov (fun k => E k a) (fun k => wE k a)
      (fun k k' Wo hWo => cE k k' Wo hWo a)
  choose e he using ce
  have G2 : ∀ (i : h.J) (i' : h'.J) (Wo : Y.H.left.Opens), Wo ≤ h.W i ⊓ h'.W i' → ∀ f,
      h.d i Wo f - h'.d i' Wo f = ∑ a, constFn Y.H.hom Wo (e a) * dd a Wo f +
        ∑ a, ∑ b, constFn Y.H.hom Wo (h.Θ a b) * dlg Y.H Y.q.left Q.P.L (dd b) (h.j i) (h'.j i') Wo * dd a Wo f := by
    intro i i' Wo hWo f
    have hk : Wo ≤ Wk (i, i') := hWo.trans (hWk (i, i')).ge
    have := PE (i, i') Wo hk f
    simp only [he, rsT_constFn _ hk] at this
    exact this

  obtain ⟨P, hP⟩ : ∃ P : K → ∀ Wo : Y.H.left.Opens, Γ(Y.H.left, Wo), ∀ k Wo, P k Wo =
      2 * (rsT (h.p k.1) Wo - rsT (h'.p k.2) Wo) + 2 * dlg Y.H Y.q.left Q.P.L (h.d k.1) (h.j k.1) (h'.j k.2) Wo -
        ∑ a, ∑ b, constFn Y.H.hom Wo (h.Θ a b) * dlg Y.H Y.q.left Q.P.L (dd a) (h.j k.1) (h'.j k.2) Wo *
          dlg Y.H Y.q.left Q.P.L (dd b) (h.j k.1) (h'.j k.2) Wo := ⟨_, fun _ _ => rfl⟩
  have rP : ∀ (k : K) (Wo : Y.H.left.Opens), Wo ≤ Wk k → rsT (P k (Wk k)) Wo = P k Wo := by
    intro k Wo hWo
    have e : ∀ b, rsT (dlg Y.H Y.q.left Q.P.L (dd b) (h.j k.1) (h'.j k.2) (Wk k)) Wo =
        dlg Y.H Y.q.left Q.P.L (dd b) (h.j k.1) (h'.j k.2) Wo := fun b =>
      rsT_dlg _ _ _ (hddF b) _ _ le_top hWo (hWU k)
    have e' : rsT (dlg Y.H Y.q.left Q.P.L (h.d k.1) (h.j k.1) (h'.j k.2) (Wk k)) Wo =
        dlg Y.H Y.q.left Q.P.L (h.d k.1) (h.j k.1) (h'.j k.2) Wo :=
      rsT_dlg _ _ _ (h.lift k.1).1 _ _ (l1 k) hWo (hWU k)
    simp only [hP, rsT_sub, rsT_add, rsT_mul, rsT_sum, rsT_two hWo, rsT_constFn _ hWo, e, e',
      rsT_rsT (l1 k) hWo, rsT_rsT (l2 k) hWo]
  have wP : ∀ k : K, IsWt Y 0 _ (P k (Wk k)) := fun k => by
    rw [hP]
    have wd : IsWt Y 0 (Wk k) (dlg Y.H Y.q.left Q.P.L (h.d k.1) (h.j k.1) (h'.j k.2) (Wk k)) :=
      wℓ k _ fun f hf => (hB k.1).2.2.2 0 (V k.1 ⊓ V' k.2) (l1 k) f hf
    have wb : ∀ b, IsWt Y 0 (Wk k) (dlg Y.H Y.q.left Q.P.L (dd b) (h.j k.1) (h'.j k.2) (Wk k)) := fun b =>
      wℓ k (dd b) fun f hf => isWt_inv (hinv b) hf
    have w2 : IsWt Y 0 (Wk k) (2 : Γ(Y.H.left, Wk k)) := by
      have := isWt_zero_constFn (Y := Y) (Wk k) 2
      rwa [constFn_two] at this
    refine isWt_sub (isWt_add (isWt_zero_mul w2 (isWt_sub (GlobalTheory.Heat.Adjust.isWt_rsT Y (l1 k) (hB k.1).2.1)
      (GlobalTheory.Heat.Adjust.isWt_rsT Y (l2 k) (hB' k.2).2.1))) (isWt_zero_mul w2 wd))
      (isWt_sum _ _ fun a _ => isWt_sum _ _ fun b _ => isWt_zero_mul (isWt_zero_mul (isWt_zero_constFn _ _) (wb a)) (wb b))
  have rel : ∀ (k k' : K) (Wo : Y.H.left.Opens), Wo ≤ Wk k ⊓ Wk k' → P k' Wo - P k Wo =
      2 * ∑ a, constFn Y.H.hom Wo (e a) * dlg Y.H Y.q.left Q.P.L (dd a) (h'.j k.2) (h'.j k'.2) Wo := by
    intro k k' Wo hWo
    have h1 : Wo ≤ Wk k := hWo.trans inf_le_left
    have h2 : Wo ≤ Wk k' := hWo.trans inf_le_right
    have a1 := h1.trans (l1 k)
    have a2 := h2.trans (l1 k')
    have b1 := h1.trans (l2 k)
    have b2 := h2.trans (l2 k')
    have w1 := W1 k.1 k'.1 Wo (le_inf a1 a2)
    have w2 := W2 k.2 k'.2 Wo (le_inf b1 b2)
    have t1 : Wo ≤ Y.q.left ⁻¹ᵁ (Q.P.L.U (h.j k.1) ⊓ Q.P.L.U (h.j k'.1) ⊓ Q.P.L.U (h'.j k.2)) :=
      le_inf (le_inf (uh a1) (uh a2)) (uh' b1)
    have t2 : Wo ≤ Y.q.left ⁻¹ᵁ (Q.P.L.U (h.j k'.1) ⊓ Q.P.L.U (h'.j k.2) ⊓ Q.P.L.U (h'.j k'.2)) :=
      le_inf (le_inf (uh a2) (uh' b1)) (uh' b2)
    have c1 : ∀ δ : Fld Y.H.left, IsDer (δ Wo) → dlg Y.H Y.q.left Q.P.L δ (h.j k.1) (h'.j k.2) Wo =
        dlg Y.H Y.q.left Q.P.L δ (h.j k.1) (h.j k'.1) Wo + dlg Y.H Y.q.left Q.P.L δ (h.j k'.1) (h'.j k.2) Wo :=
      fun δ hδ => dlg_cocycle Y.H Y.q.left Q.P.L hL _ _ _ hδ t1
    have c2 : ∀ δ : Fld Y.H.left, IsDer (δ Wo) → dlg Y.H Y.q.left Q.P.L δ (h.j k'.1) (h'.j k'.2) Wo =
        dlg Y.H Y.q.left Q.P.L δ (h.j k'.1) (h'.j k.2) Wo + dlg Y.H Y.q.left Q.P.L δ (h'.j k.2) (h'.j k'.2) Wo :=
      fun δ hδ => dlg_cocycle Y.H Y.q.left Q.P.L hL _ _ _ hδ t2
    have hd1 : IsDer (h.d k.1 Wo) := isDer_of_isField (h.lift k.1).1 a1
    have hd2 : IsDer (h.d k'.1 Wo) := isDer_of_isField (h.lift k'.1).1 a2

    have KSx : dlg Y.H Y.q.left Q.P.L (h.d k.1) (h.j k'.1) (h'.j k.2) Wo -
        dlg Y.H Y.q.left Q.P.L (h.d k'.1) (h.j k'.1) (h'.j k.2) Wo =
        ∑ a, ∑ b, constFn Y.H.hom Wo (h.Θ a b) * dlg Y.H Y.q.left Q.P.L (dd b) (h.j k.1) (h.j k'.1) Wo *
          dlg Y.H Y.q.left Q.P.L (dd a) (h.j k'.1) (h'.j k.2) Wo := by
      have := w1.1 (pbT Y.q.left (Q.P.L.g (h.j k'.1) (h'.j k.2)).val Wo)
      unfold dlg at this ⊢
      rw [← sub_mul, this, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun b _ => by ring
    have KSz : dlg Y.H Y.q.left Q.P.L (h.d k'.1) (h'.j k.2) (h'.j k'.2) Wo -
        dlg Y.H Y.q.left Q.P.L (h'.d k.2) (h'.j k.2) (h'.j k'.2) Wo =
        ∑ a, constFn Y.H.hom Wo (e a) * dlg Y.H Y.q.left Q.P.L (dd a) (h'.j k.2) (h'.j k'.2) Wo +
        ∑ a, ∑ b, constFn Y.H.hom Wo (h.Θ a b) * dlg Y.H Y.q.left Q.P.L (dd b) (h.j k'.1) (h'.j k.2) Wo *
          dlg Y.H Y.q.left Q.P.L (dd a) (h'.j k.2) (h'.j k'.2) Wo := by
      have := G2 k'.1 k.2 Wo (le_inf a2 b1) (pbT Y.q.left (Q.P.L.g (h'.j k.2) (h'.j k'.2)).val Wo)
      unfold dlg at this ⊢
      rw [← sub_mul, this, add_mul, Finset.sum_mul, Finset.sum_mul]
      congr 1
      · exact Finset.sum_congr rfl fun a _ => by ring
      · refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun b _ => by ring
    have q1 := quad_add (hs Wo) (fun a => dlg Y.H Y.q.left Q.P.L (dd a) (h.j k.1) (h.j k'.1) Wo)
      (fun a => dlg Y.H Y.q.left Q.P.L (dd a) (h.j k'.1) (h'.j k.2) Wo)
    have q2 := quad_add (hs Wo) (fun a => dlg Y.H Y.q.left Q.P.L (dd a) (h.j k'.1) (h'.j k.2) Wo)
      (fun a => dlg Y.H Y.q.left Q.P.L (dd a) (h'.j k.2) (h'.j k'.2) Wo)
    rw [hP, hP, c1 _ hd1, c2 _ hd2]
    simp only [c1 _ (hdd _ Wo), c2 _ (hdd _ Wo)]
    rw [q1, q2]
    linear_combination -w1.2.1 + w2.2.1 - 2 * KSx + 2 * KSz
  have G1 := GlobalTheory.T.invariantField_comb_kills_weightZero_of_coboundary R Q O oa Y n v dd hinv K Wk (fun k => h'.j k.2) (fun k => ⟨_, rfl⟩) hcov
    (fun k => (hWU k).trans (Y.q.left.preimage_mono inf_le_right))
    (fun k => constFn Y.H.hom (Wk k) (algebraMap ℚ R (1 / 2)) * P k (Wk k)) e
    (fun k => isWt_zero_mul (isWt_zero_constFn _ _) (wP k)) (fun k k' Wo hWo => by
      simp only [rsT_mul, rsT_constFn _ (hWo.trans inf_le_left), rsT_constFn _ (hWo.trans inf_le_right),
        rP k Wo (hWo.trans inf_le_left), rP k' Wo (hWo.trans inf_le_right)]
      rw [← mul_sub, rel k k' Wo hWo, ← _root_.mul_assoc, mul_comm (constFn _ _ _), two, _root_.one_mul])

  have kill : ∀ (i₁ i₂ : h'.J) (Wo : Y.H.left.Opens), Wo ≤ h'.W i₁ → Wo ≤ h'.W i₂ →
      ∑ a, constFn Y.H.hom Wo (e a) * dlg Y.H Y.q.left Q.P.L (dd a) (h'.j i₁) (h'.j i₂) Wo = 0 := by
    intro i₁ i₂ Wo hw₁ hw₂
    have hWo : Wo ≤ Y.q.left ⁻¹ᵁ (Q.P.L.U (h'.j i₁) ⊓ Q.P.L.U (h'.j i₂)) := le_inf (uh' hw₁) (uh' hw₂)
    have g := G1 (Q.P.L.U (h'.j i₁) ⊓ Q.P.L.U (h'.j i₂))
      (pbT Y.q.left (Q.P.L.g (h'.j i₁) (h'.j i₂)).val (Y.q.left ⁻¹ᵁ (Q.P.L.U (h'.j i₁) ⊓ Q.P.L.U (h'.j i₂))))
      (isWt_zero_pbT _ le_rfl)
    have g' := congrArg (fun s => rsT s Wo) g
    have e1 : ∀ a, rsT (constFn Y.H.hom (Y.q.left ⁻¹ᵁ (Q.P.L.U (h'.j i₁) ⊓ Q.P.L.U (h'.j i₂))) (e a) *
        dd a _ (pbT Y.q.left (Q.P.L.g (h'.j i₁) (h'.j i₂)).val (Y.q.left ⁻¹ᵁ (Q.P.L.U (h'.j i₁) ⊓ Q.P.L.U (h'.j i₂))))) Wo =
        constFn Y.H.hom Wo (e a) * dd a Wo (pbT Y.q.left (Q.P.L.g (h'.j i₁) (h'.j i₂)).val Wo) := fun a => by
      rw [rsT_mul, rsT_constFn _ hWo, ← field_rsT (hddF a) le_top hWo, rsT_pbT _ le_rfl hWo]
    simp only [rsT_sum, rsT_zero, e1] at g'
    unfold dlg
    have := congrArg (· * pbT Y.q.left (Q.P.L.g (h'.j i₁) (h'.j i₂))⁻¹.val Wo) g'
    simp only [zero_mul, Finset.sum_mul] at this
    rw [← this]
    exact Finset.sum_congr rfl fun a _ => by ring

  obtain ⟨r₂, hr₂⟩ := GlobalTheory.T.raynaud_weight_zero_compatible_functions_eq_base_constant R Q O oa Y K Wk (fun k => ⟨_, rfl⟩) hcov (fun k => P k (Wk k)) wP
    (fun k k' Wo hWo => by
      rw [rP k Wo (hWo.trans inf_le_left), rP k' Wo (hWo.trans inf_le_right)]
      have := rel k k' Wo hWo
      rw [kill k.2 k'.2 Wo (hWo.trans (inf_le_left.trans (l2 k))) (hWo.trans (inf_le_right.trans (l2 k')))] at this
      linear_combination -this)

  obtain ⟨Pq, hPq⟩ : ∃ Pq : K → ∀ Wo : Y.H.left.Opens, Γ(Y.H.left, Wo), ∀ k Wo, Pq k Wo =
      2 * (rsT (h.p' k.1) Wo - rsT (h'.p' k.2) Wo) +
        2 * ∑ a, constFn Y.H.hom Wo (h.u a) * dlg Y.H Y.q.left Q.P.L (dd a) (h.j k.1) (h'.j k.2) Wo -
        ∑ a, ∑ b, constFn Y.H.hom Wo (h.Θ a b) * dd a Wo (dlg Y.H Y.q.left Q.P.L (dd b) (h.j k.1) (h'.j k.2) Wo) :=
    ⟨_, fun _ _ => rfl⟩
  have rQ : ∀ (k : K) (Wo : Y.H.left.Opens), Wo ≤ Wk k → rsT (Pq k (Wk k)) Wo = Pq k Wo := by
    intro k Wo hWo
    have e : ∀ b, rsT (dlg Y.H Y.q.left Q.P.L (dd b) (h.j k.1) (h'.j k.2) (Wk k)) Wo =
        dlg Y.H Y.q.left Q.P.L (dd b) (h.j k.1) (h'.j k.2) Wo := fun b =>
      rsT_dlg _ _ _ (hddF b) _ _ le_top hWo (hWU k)
    have e2 : ∀ a b, rsT (dd a (Wk k) (dlg Y.H Y.q.left Q.P.L (dd b) (h.j k.1) (h'.j k.2) (Wk k))) Wo =
        dd a Wo (dlg Y.H Y.q.left Q.P.L (dd b) (h.j k.1) (h'.j k.2) Wo) := fun a b => by
      rw [← field_rsT (hddF a) le_top hWo, e b]
    simp only [hPq, rsT_sub, rsT_add, rsT_mul, rsT_sum, rsT_two hWo, rsT_constFn _ hWo, e, e2,
      rsT_rsT (l1 k) hWo, rsT_rsT (l2 k) hWo]
  have wQ : ∀ k : K, IsWt Y 0 _ (Pq k (Wk k)) := fun k => by
    rw [hPq]
    have wb : ∀ b, IsWt Y 0 (Wk k) (dlg Y.H Y.q.left Q.P.L (dd b) (h.j k.1) (h'.j k.2) (Wk k)) := fun b =>
      wℓ k (dd b) fun f hf => isWt_inv (hinv b) hf
    have w2 : IsWt Y 0 (Wk k) (2 : Γ(Y.H.left, Wk k)) := by
      have := isWt_zero_constFn (Y := Y) (Wk k) 2
      rwa [constFn_two] at this
    refine isWt_sub (isWt_add (isWt_zero_mul w2 (isWt_sub (GlobalTheory.Heat.Adjust.isWt_rsT Y (l1 k) (hB k.1).2.2.1)
      (GlobalTheory.Heat.Adjust.isWt_rsT Y (l2 k) (hB' k.2).2.2.1)))
      (isWt_zero_mul w2 (isWt_sum _ _ fun a _ => isWt_zero_mul (isWt_zero_constFn _ _) (wb a))))
      (isWt_sum _ _ fun a _ => isWt_sum _ _ fun b _ => isWt_zero_mul (isWt_zero_constFn _ _) (isWt_inv (hinv a) (wb b)))
  obtain ⟨r₁, hr₁⟩ := GlobalTheory.T.raynaud_weight_zero_compatible_functions_eq_base_constant R Q O oa Y K Wk (fun k => ⟨_, rfl⟩) hcov (fun k => Pq k (Wk k)) wQ
    (fun k k' Wo hWo => by
      rw [rQ k Wo (hWo.trans inf_le_left), rQ k' Wo (hWo.trans inf_le_right)]
      have h1 : Wo ≤ Wk k := hWo.trans inf_le_left
      have h2 : Wo ≤ Wk k' := hWo.trans inf_le_right
      have a1 := h1.trans (l1 k)
      have a2 := h2.trans (l1 k')
      have b1 := h1.trans (l2 k)
      have b2 := h2.trans (l2 k')
      have w1 := (W1 k.1 k'.1 Wo (le_inf a1 a2)).2.2
      have w2 := (W2 k.2 k'.2 Wo (le_inf b1 b2)).2.2
      have t1 : Wo ≤ Y.q.left ⁻¹ᵁ (Q.P.L.U (h.j k.1) ⊓ Q.P.L.U (h.j k'.1) ⊓ Q.P.L.U (h'.j k.2)) :=
        le_inf (le_inf (uh a1) (uh a2)) (uh' b1)
      have t2 : Wo ≤ Y.q.left ⁻¹ᵁ (Q.P.L.U (h.j k'.1) ⊓ Q.P.L.U (h'.j k.2) ⊓ Q.P.L.U (h'.j k'.2)) :=
        le_inf (le_inf (uh a2) (uh' b1)) (uh' b2)
      have c1 : ∀ b, dlg Y.H Y.q.left Q.P.L (dd b) (h.j k.1) (h'.j k.2) Wo =
          dlg Y.H Y.q.left Q.P.L (dd b) (h.j k.1) (h.j k'.1) Wo + dlg Y.H Y.q.left Q.P.L (dd b) (h.j k'.1) (h'.j k.2) Wo :=
        fun b => dlg_cocycle Y.H Y.q.left Q.P.L hL _ _ _ (hdd b Wo) t1
      have c2 : ∀ b, dlg Y.H Y.q.left Q.P.L (dd b) (h.j k'.1) (h'.j k'.2) Wo =
          dlg Y.H Y.q.left Q.P.L (dd b) (h.j k'.1) (h'.j k.2) Wo + dlg Y.H Y.q.left Q.P.L (dd b) (h'.j k.2) (h'.j k'.2) Wo :=
        fun b => dlg_cocycle Y.H Y.q.left Q.P.L hL _ _ _ (hdd b Wo) t2
      have dadd : ∀ a (x y : Γ(Y.H.left, Wo)), dd a Wo (x + y) = dd a Wo x + dd a Wo y := fun a => (hdd a Wo).1
      rw [hPq, hPq]
      simp only [c1, c2, dadd, mul_add, Finset.sum_add_distrib]
      linear_combination w1 - w2)
  refine ⟨e, algebraMap ℚ R (1 / 2) * r₂, algebraMap ℚ R (1 / 2) * r₁, G1, fun i i' Wo hWo => ⟨G2 i i' Wo hWo, ?_, ?_⟩⟩
  · have hk : Wo ≤ Wk (i, i') := hWo.trans (hWk (i, i')).ge
    have := rP (i, i') Wo hk
    rw [hr₂, rsT_constFn _ hk, hP] at this
    rw [constFn_mul, ← _root_.mul_assoc, two Wo, _root_.one_mul]
    exact this.symm
  · have hk : Wo ≤ Wk (i, i') := hWo.trans (hWk (i, i')).ge
    have := rQ (i, i') Wo hk
    rw [hr₁, rsT_constFn _ hk, hPq] at this
    rw [constFn_mul, ← _root_.mul_assoc, two Wo, _root_.one_mul]
    exact this.symm

end GlobalTheory.HeatUniqGlob
