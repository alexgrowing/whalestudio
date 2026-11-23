import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResV
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LeISupInfPreimage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BasisTangentModuleLocalizedAbelianLocusStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KS

noncomputable section

namespace GlobalTheory.CechH1Local

local macro "opens_le" : tactic =>
  `(tactic| (rw [SetLike.le_def]; intro y hy; simp only [TopologicalSpace.Opens.mem_inf] at hy ⊢; aesop))

theorem isCob_of_refine_le {Y : Scheme.{0}} {I K : Type} (Uc : I → Y.Opens) (c : C1 Uc) (hc : IsCoc Uc c)
    (V : K → Y.Opens) (σ : K → I) (hV : ∀ p, V p ≤ Uc (σ p)) (hVt : ∀ i, Uc i ≤ ⨆ p, V p)
    (B : ∀ p, Γ(Y, V p)) (hB : ∀ p p', rsT (c (σ p) (σ p')) (V p ⊓ V p') =
      rsT (B p') (V p ⊓ V p') - rsT (B p) (V p ⊓ V p')) : IsCob Uc c := by
  have hV' : ∀ p y, y ∈ V p → y ∈ Uc (σ p) := fun p y h => hV p h
  have cov : ∀ O : Y.Opens, O ≤ ⨆ p, V p → O ≤ ⨆ p, O ⊓ V p := by
    intro O hO x hx
    obtain ⟨p, hp⟩ := TopologicalSpace.Opens.mem_iSup.1 (hO hx)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨p, hx, hp⟩
  have glue : ∀ i, ∃ t : Γ(Y, Uc i), ∀ p, rsT t (Uc i ⊓ V p) =
      rsT (B p) (Uc i ⊓ V p) + rsT (c (σ p) i) (Uc i ⊓ V p) := by
    intro i
    refine exists_rsT_eq (fun p => Uc i ⊓ V p) (fun p => inf_le_left) (cov _ (hVt i)) _ fun p p' => ?_
    have h1 := congrArg (fun s => rsT s ((Uc i ⊓ V p) ⊓ (Uc i ⊓ V p'))) (hB p p')
    have h2 := congrArg (fun s => rsT s ((Uc i ⊓ V p) ⊓ (Uc i ⊓ V p'))) (hc (σ p) (σ p') i)
    simp only [rsT_add, rsT_sub] at h1 h2 ⊢
    simp (disch := opens_le) only [rsT_rsT] at h1 h2 ⊢
    linear_combination h1 - h2
  choose t ht using glue
  refine ⟨t, fun i j => ?_⟩
  refine eq_of_rsT_eq (fun p => Uc i ⊓ Uc j ⊓ V p) (fun p => inf_le_left)
    (cov _ (inf_le_left.trans (hVt i))) _ _ fun p => ?_
  have h1 := congrArg (fun s => rsT s (Uc i ⊓ Uc j ⊓ V p)) (ht i p)
  have h2 := congrArg (fun s => rsT s (Uc i ⊓ Uc j ⊓ V p)) (ht j p)
  have h3 := congrArg (fun s => rsT s (Uc i ⊓ Uc j ⊓ V p)) (hc (σ p) i j)
  simp only [rsT_add, rsT_sub] at h1 h2 h3 ⊢
  simp (disch := opens_le) only [rsT_rsT] at h1 h2 h3 ⊢
  linear_combination h1 - h2 + h3

theorem rsT_field {Z : Scheme.{0}} {d : ∀ W : Z.Opens, Γ(Z, W) → Γ(Z, W)} (hd : IsField ⊤ d) {O O' : Z.Opens}
    (h : O' ≤ O) (f : Γ(Z, O)) : rsT (d O f) O' = d O' (rsT f O') := by
  rw [rsT_of_le h, rsT_of_le h, hd.2.2 _ _ h le_top]

theorem rsT_appLE {Y X : Scheme.{0}} (π : Y ⟶ X) (V : X.Opens) {O O' : Y.Opens} (h : O ≤ π ⁻¹ᵁ V) (h' : O' ≤ O)
    (r : Γ(X, V)) : rsT ((π.appLE V O h).hom r) O' = (π.appLE V O' (h'.trans h)).hom r := by
  rw [rsT_of_le h']
  exact congrArg (fun φ => φ.hom r) (Scheme.Hom.appLE_map π h (homOfLE h').op)

theorem rsT_unit {Z : Scheme.{0}} {T O : Z.Opens} (h : O ≤ T) (u : Γ(Z, T)ˣ) :
    rsT u.val O * rsT u⁻¹.val O = 1 := by
  rw [← rsT_mul, Units.mul_inv, rsT_one h]

theorem isCoc_dlg {Z : Scheme.{0}} (L : LB Z) (hL : L.IsLB) {d : ∀ W : Z.Opens, Γ(Z, W) → Γ(Z, W)}
    (hd : IsField ⊤ d) {J : Type} (W : J → Z.Opens) (j : J → L.ι) (hj : ∀ i, W i ≤ L.U (j i)) :
    IsCoc W (fun i i' => d (W i ⊓ W i') (rsT (L.g (j i) (j i')).val (W i ⊓ W i')) *
      rsT (L.g (j i) (j i'))⁻¹.val (W i ⊓ W i')) := by
  intro i i' i''
  set O := W i ⊓ W i' ⊓ W i''
  have l₁ : O ≤ W i ⊓ W i' := inf_le_left
  have l₂ : O ≤ W i' ⊓ W i'' := le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have l₃ : O ≤ W i ⊓ W i'' := le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have m₁ : W i ⊓ W i' ≤ L.U (j i) ⊓ L.U (j i') := inf_le_inf (hj i) (hj i')
  have m₂ : W i' ⊓ W i'' ≤ L.U (j i') ⊓ L.U (j i'') := inf_le_inf (hj i') (hj i'')
  have m₃ : W i ⊓ W i'' ≤ L.U (j i) ⊓ L.U (j i'') := inf_le_inf (hj i) (hj i'')
  have k : ∀ (a b : J) (l : O ≤ W a ⊓ W b) (m : W a ⊓ W b ≤ L.U (j a) ⊓ L.U (j b)),
      rsT (d (W a ⊓ W b) (rsT (L.g (j a) (j b)).val (W a ⊓ W b)) * rsT (L.g (j a) (j b))⁻¹.val (W a ⊓ W b)) O =
        d O (rsT (L.g (j a) (j b)).val O) * rsT (L.g (j a) (j b))⁻¹.val O := by
    intro a b l m
    rw [rsT_mul, rsT_field hd l, rsT_rsT m l, rsT_rsT m l]
  rw [k i i' l₁ m₁, k i' i'' l₂ m₂, k i i'' l₃ m₃]
  have T3 : O ≤ L.U (j i) ⊓ L.U (j i') ⊓ L.U (j i'') :=
    le_inf (le_inf (l₁.trans (m₁.trans inf_le_left)) (l₁.trans (m₁.trans inf_le_right)))
      (l₂.trans (m₂.trans inf_le_right))
  have co := congrArg (fun u => rsT (Units.val u) O) (hL.cocycle (j i) (j i') (j i''))
  simp only [Units.val_mul, rsT_mul] at co
  have e : ∀ {T T' : Z.Opens} (h : T' ≤ T) (u : Γ(Z, T)ˣ), (res h u).val = resG Z h u.val := fun _ _ => rfl
  have r : ∀ {T T' : Z.Opens} (h : T' ≤ T) (s : Γ(Z, T)), O ≤ T' → rsT (resG Z h s) O = rsT s O :=
    fun h s hO => by rw [← rsT_of_le h, rsT_rsT h hO]
  rw [e, e, e, r _ _ T3, r _ _ T3, r _ _ T3] at co
  set a := rsT (L.g (j i) (j i')).val O
  set b := rsT (L.g (j i') (j i'')).val O
  set a' := rsT (L.g (j i) (j i'))⁻¹.val O
  set b' := rsT (L.g (j i') (j i''))⁻¹.val O
  set e' := rsT (L.g (j i) (j i''))⁻¹.val O
  have ha : a * a' = 1 := rsT_unit (l₁.trans m₁) _
  have hb : b * b' = 1 := rsT_unit (l₂.trans m₂) _
  have he : rsT (L.g (j i) (j i'')).val O * e' = 1 := rsT_unit (l₃.trans m₃) _
  rw [← co] at he ⊢
  have hdm := hd.2.1 O le_top a b
  rw [hdm]
  linear_combination (-(d O a * a' + d O b * b')) * he + (d O a * b * e') * ha + (d O b * a * e') * hb

theorem exists_dlog_add_coboundary_abLocus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R), (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → ∀ (c : R), c = ∏ i, tt i → ∀ (n : ℕ) (v' : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G)) (dd' : Fin n → Fld t.G.left), (∀ a, IsInv t.G (v' a) (dd' a)) → ∀ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι) (hW : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1), ⨆ i, W i = t.G.hom ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1 → (∀ i, W i ≤ t.PP.L.U (j i)) → ∀ z : C1 W, IsCoc W z → ∃ (cc : Fin n → Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)) (y : ∀ i, Γ(t.G.left, W i)), ∀ i i', z i i' = ∑ b, GlobalTheory.HeatV.cst t.G.hom (GlobalTheory.HeatV.bo R c).1 (inf_le_left.trans (hW i)) (cc b) * (dd' b (W i ⊓ W i') (rsT (t.PP.L.g (j i) (j i')).val (W i ⊓ W i')) * rsT (t.PP.L.g (j i) (j i'))⁻¹.val (W i ⊓ W i')) + (rsT (y i') (W i ⊓ W i') - rsT (y i) (W i ⊓ W i')) := by
  intro E _ _ _ H R _ _ _ _ _ _ t P m tt htt hab c hc n v' dd' hdd J W j hW hWc hj z hz
  let K := {p : t.G.left.affineOpens × J // p.1.1 ≤ W p.2}
  let V : K → t.G.left.Opens := fun p => p.1.1.1
  let σ : K → J := fun p => p.1.2
  have hVσ : ∀ p, V p ≤ W (σ p) := fun p => p.2
  have hVt : ∀ i, W i ≤ ⨆ p, V p := by
    intro i x hx
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUW⟩ := t.G.left.isBasis_affineOpens.exists_subset_of_mem_open hx (W i).isOpen
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨(⟨U, hU⟩, i), hUW⟩, hxU⟩
  have cover : ⨆ p, V p = t.G.hom ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1 := by
    refine le_antisymm (iSup_le fun p => (hVσ p).trans (hW _)) ?_
    rw [← hWc]
    exact iSup_le hVt
  let z' : C1 V := fun p p' => rsT (z (σ p) (σ p')) (V p ⊓ V p')
  have hz' : IsCoc V z' := by
    intro p p' p''
    have h := congrArg (fun s => rsT s (V p ⊓ V p' ⊓ V p'')) (hz (σ p) (σ p') (σ p''))
    simp only [rsT_add] at h
    have l₁ : V p ⊓ V p' ⊓ V p'' ≤ W (σ p) ⊓ W (σ p') ⊓ W (σ p'') :=
      inf_le_inf (inf_le_inf (hVσ p) (hVσ p')) (hVσ p'')
    simp only [z']
    rw [rsT_rsT (inf_le_inf (hVσ p) (hVσ p')) inf_le_left, rsT_rsT (inf_le_inf (hVσ p') (hVσ p''))
      (le_inf (inf_le_left.trans inf_le_right) inf_le_right),
      rsT_rsT (inf_le_inf (hVσ p) (hVσ p'')) (le_inf (inf_le_left.trans inf_le_left) inf_le_right)]
    rwa [rsT_rsT inf_le_left l₁, rsT_rsT (le_inf (inf_le_left.trans inf_le_right) inf_le_right) l₁,
      rsT_rsT (le_inf (inf_le_left.trans inf_le_left) inf_le_right) l₁] at h
  obtain ⟨cc, y', hy'⟩ := GlobalTheory.T.basis_tangent_module_localized_abelian_locus E H R t P m tt htt hab c hc n v' dd' hdd K V (fun p => j (σ p))
    (fun p => (hVσ p).trans (hW _)) cover (fun p => (hVσ p).trans (hj _)) (fun p => p.1.1.2) z' hz'
  let dl : Fin n → C1 W := fun b i i' => dd' b (W i ⊓ W i') (rsT (t.PP.L.g (j i) (j i')).val (W i ⊓ W i')) *
    rsT (t.PP.L.g (j i) (j i'))⁻¹.val (W i ⊓ W i')
  have hdl : ∀ b, IsCoc W (dl b) := fun b => isCoc_dlg t.PP.L t.PP.isLB (hdd b).1 W j hj
  let c0 : C1 W := fun i i' => z i i' - ∑ b, GlobalTheory.HeatV.cst t.G.hom (GlobalTheory.HeatV.bo R c).1
    (inf_le_left.trans (hW i)) (cc b) * dl b i i'
  let Cf : ∀ O : t.G.left.Opens, O ≤ t.G.hom ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1 → Fin n → Γ(t.G.left, O) :=
    fun O h b => (t.G.hom.appLE _ O h).hom (cc b)
  have key : ∀ (a a' : J) {O : t.G.left.Opens} (l : O ≤ W a ⊓ W a'),
      rsT (c0 a a') O = rsT (z a a') O - ∑ b, Cf O (l.trans (inf_le_left.trans (hW a))) b * rsT (dl b a a') O := by
    intro a a' O l
    simp only [c0]
    rw [rsT_sub, rsT_sum]
    congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [rsT_mul, rsT_appLE _ _ _ l]
  have hc0 : IsCoc W c0 := by
    intro i i' i''
    have l₁ : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i' := inf_le_left
    have l₂ : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'' := le_inf (inf_le_left.trans inf_le_right) inf_le_right
    have l₃ : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'' := le_inf (inf_le_left.trans inf_le_left) inf_le_right
    have h0 := hz i i' i''
    rw [key i i' l₁, key i' i'' l₂, key i i'' l₃]
    have hs : ∑ b, Cf _ (l₁.trans (inf_le_left.trans (hW i))) b * rsT (dl b i i') (W i ⊓ W i' ⊓ W i'') +
        ∑ b, Cf _ (l₁.trans (inf_le_left.trans (hW i))) b * rsT (dl b i' i'') (W i ⊓ W i' ⊓ W i'') =
        ∑ b, Cf _ (l₁.trans (inf_le_left.trans (hW i))) b * rsT (dl b i i'') (W i ⊓ W i' ⊓ W i'') := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [← mul_add, hdl b i i' i'']
    linear_combination h0 - hs
  have hB : ∀ p p', rsT (c0 (σ p) (σ p')) (V p ⊓ V p') = rsT (y' p') (V p ⊓ V p') - rsT (y' p) (V p ⊓ V p') := by
    intro p p'
    have l : V p ⊓ V p' ≤ W (σ p) ⊓ W (σ p') := inf_le_inf (hVσ p) (hVσ p')
    rw [key _ _ l, show rsT (z (σ p) (σ p')) (V p ⊓ V p') = z' p p' from rfl, hy' p p']
    have hs : ∀ b, rsT (dl b (σ p) (σ p')) (V p ⊓ V p') =
        dd' b (V p ⊓ V p') (rsT (t.PP.L.g (j (σ p)) (j (σ p'))).val (V p ⊓ V p')) *
          rsT (t.PP.L.g (j (σ p)) (j (σ p')))⁻¹.val (V p ⊓ V p') := fun b => by
      simp only [dl]
      rw [rsT_mul, rsT_field (hdd b).1 l, rsT_rsT (inf_le_inf (hj _) (hj _)) l, rsT_rsT (inf_le_inf (hj _) (hj _)) l]
    simp only [hs]
    ring
  obtain ⟨y, hy⟩ := isCob_of_refine_le W c0 hc0 V σ hVσ hVt y' hB
  refine ⟨cc, y, fun i i' => ?_⟩
  have := hy i i'
  simp only [c0] at this
  linear_combination this

end GlobalTheory.CechH1Local
