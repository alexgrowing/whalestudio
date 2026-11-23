import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open GlobalTheory.GalV (HTower Splits)
open UpperTheory.Gal.crystallineComparison.Mod (Std TjD TjE KSOKE)
open scoped TensorProduct
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.Int.Geo

namespace UpperTheory.TraceConjugationCover

section Lat

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} {L : Link D G}

private theorem conj_mem {N : ℕ} {k u : G.GAf} (hk : k ∈ L.KN 1) (hu : u ∈ L.KN N) : k * u * k⁻¹ ∈ L.KN N := by
  have key : ∀ u : G.GAf, L.CongOne N u → L.CongOne N (k * u * k⁻¹) := by
    intro u hu v hv
    obtain ⟨w, hw, e⟩ := hu _ (integ_of_mem (inv_mem hk) v hv)
    refine ⟨L.actG k w, integ_of_mem hk w hw, ?_⟩
    have h1 : L.actG (k * u * k⁻¹) v = L.actG k (L.actG u (L.actG k⁻¹ v)) := by
      simp only [map_mul, Module.End.mul_apply]
    have h2 : L.actG k (L.actG k⁻¹ v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [h1, e, map_add, map_nsmul, h2]
  refine ⟨key _ hu.1, ?_⟩
  have : (k * u * k⁻¹)⁻¹ = k * u⁻¹ * k⁻¹ := by group
  rw [this]
  exact key _ hu.2

private theorem mulF_nat (n : ℕ) (y : 𝓞 D.F) {v : AfP p ⊗[ℚ] VQ D} (hv : v ∈ LaHat D) :
    mulF D ((n : 𝓞 D.F) * y) v = n • mulF D y v ∧ mulF D y v ∈ LaHat D := by
  induction hv using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, x, ha, rfl⟩ := hz
    have e : ∀ c : 𝓞 D.F, mulF D c (a ⊗ₜ ((1 : ℚ) ⊗ₜ x)) = a ⊗ₜ ((1 : ℚ) ⊗ₜ (algebraMap (𝓞 D.F) D.O c • x)) := by
      intro c
      simp [mulF, actQ, LinearMap.baseChange_tmul]
      rfl
    refine ⟨?_, ?_⟩
    · rw [e, e, map_mul, map_natCast, mul_smul, Nat.cast_smul_eq_nsmul, TensorProduct.tmul_smul, TensorProduct.tmul_smul]
    · rw [e]
      exact AddSubgroup.subset_closure ⟨a, _, ha, rfl⟩
  | zero => simp
  | add x y _ _ hx hy =>
    refine ⟨?_, ?_⟩
    · rw [map_add, map_add, hx.1, hy.1, smul_add]
    · rw [map_add]; exact add_mem hx.2 hy.2
  | neg x _ hx =>
    refine ⟨?_, ?_⟩
    · rw [map_neg, map_neg, hx.1, smul_neg]
    · rw [map_neg]; exact neg_mem hx.2

private theorem idHat_le {N₀ : ℕ} {𝔞 : Ideal (𝓞 D.F)} {z : AfP p ⊗[ℚ] VQ D}
    (hz : z ∈ idHat D (Ideal.span {(N₀ : 𝓞 D.F)} * 𝔞)) : ∃ w ∈ LaHat D, z = N₀ • w := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨x, hx, v, hv, rfl⟩ := hz
    obtain ⟨y, -, rfl⟩ := Ideal.mem_span_singleton_mul.1 hx
    exact ⟨_, (mulF_nat N₀ y hv).2, (mulF_nat N₀ y hv).1⟩
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    exact ⟨a + b, add_mem ha hb, by rw [smul_add]⟩
  | neg x _ hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    exact ⟨-a, neg_mem ha, by rw [smul_neg]⟩

private theorem lev_le {N₀ : ℕ} {𝔞 : Ideal (𝓞 D.F)} {K₀ : Subgroup G.GAf}
    (h : IsLev L (Ideal.span {(N₀ : 𝓞 D.F)} * 𝔞) K₀) : K₀ ≤ L.KN N₀ := by
  have key : ∀ g ∈ K₀, L.CongOne N₀ g := by
    intro g hg v hv
    obtain ⟨w, hw, e⟩ := idHat_le (((h g).1 hg).2 v hv)
    exact ⟨w, hw, by rw [← e]; abel⟩
  exact fun g hg => ⟨key g hg, key _ (inv_mem hg)⟩

end Lat

section Tw

variable {B : Scheme.{0}} {Γ : Type} [Group Γ]

private structure Dat (X : UpperTheory.Gal.G3.Tower B Γ) (i : X.ι) (K₀ : Subgroup Γ) : Prop where
  le : X.K i ≤ K₀
  mem : ∀ k ∈ K₀, k ∈ X.Δ
  nrm : ∀ k ∈ K₀, ∀ u ∈ X.K i, k * u * k⁻¹ ∈ X.K i

variable {X : UpperTheory.Gal.G3.Tower B Γ} {i : X.ι} {K₀ : Subgroup Γ} (d : Dat X i K₀)

private def trK (x : K₀) : X.Z i ⟶ X.Z i := X.tr i i x (d.mem _ x.2) (d.nrm _ x.2)

private theorem trK_mul (x y : K₀) : trK d x ≫ trK d y = trK d (y * x) := X.tr_mul ..

private theorem trK_self (x : K₀) (hx : (x : Γ) ∈ X.K i) : trK d x = 𝟙 _ := X.tr_self _ _ _ _ hx

private theorem trK_mk {x y : K₀} (h : (x : K₀ ⧸ (X.K i).subgroupOf K₀) = y) : trK d x = trK d y := by
  have hu : ((x⁻¹ * y : K₀) : Γ) ∈ X.K i := Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 h)
  calc trK d x = trK d (x⁻¹ * y) ≫ trK d x := by rw [trK_self d _ hu, Category.id_comp]
    _ = trK d y := by rw [trK_mul, mul_inv_cancel_left]

variable [((X.K i).subgroupOf K₀).Normal]

private def act (δ : K₀ ⧸ (X.K i).subgroupOf K₀) : X.Z i ⟶ X.Z i := trK d (δ⁻¹).out

private theorem act_mk (u : K₀) : act d (((u⁻¹ : K₀) : K₀ ⧸ (X.K i).subgroupOf K₀)) = trK d u :=
  trK_mk d (by rw [QuotientGroup.out_eq', ← QuotientGroup.mk_inv, inv_inv])

private theorem act_one : act d 1 = 𝟙 _ := by
  have h := act_mk d (1 : K₀)
  rw [inv_one, QuotientGroup.mk_one] at h
  rw [h]
  exact trK_self d _ (one_mem _)

private theorem act_mul (g h : K₀ ⧸ (X.K i).subgroupOf K₀) : act d (g * h) = act d g ≫ act d h := by
  rw [act, act, act, trK_mul]
  refine trK_mk d ?_
  rw [QuotientGroup.out_eq', QuotientGroup.mk_mul, QuotientGroup.out_eq', QuotientGroup.out_eq', mul_inv_rev]

private theorem act_q (δ : K₀ ⧸ (X.K i).subgroupOf K₀) : act d δ ≫ X.q i = X.q i := X.tr_q ..

private theorem act_inj {j : X.ι} (hj : K₀ ≤ X.K j) (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    (z : UpperTheory.Gal.G3.sp Ω ⟶ X.Z i) (δ δ' : K₀ ⧸ (X.K i).subgroupOf K₀) (h : z ≫ act d δ = z ≫ act d δ') : δ = δ' := by
  have h' : z ≫ trK d (δ⁻¹).out = z ≫ trK d (δ'⁻¹).out := h
  set x := (δ⁻¹).out with hx
  set y := (δ'⁻¹).out with hy
  have e : z ≫ trK d (x⁻¹ * y) = z := by
    rw [← trK_mul, ← Category.assoc, ← h', Category.assoc, trK_mul, inv_mul_cancel,
      trK_self d _ (one_mem _), Category.comp_id]
  have hm : ((x⁻¹ * y : K₀) : Γ) ∈ X.K i :=
    X.free i j (d.le.trans hj) _ (hj (x⁻¹ * y).2) _ _ Ω z e
  have hq : (x : K₀ ⧸ (X.K i).subgroupOf K₀) = y := QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 hm)
  rw [hx, hy, QuotientGroup.out_eq', QuotientGroup.out_eq'] at hq
  exact inv_injective hq

omit [((X.K i).subgroupOf K₀).Normal] in
include d in
private theorem fin_quot {j : X.ι} (hj : K₀ ≤ X.K j) : Finite (K₀ ⧸ (X.K i).subgroupOf K₀) := by
  have h := X.idx i j
  rw [← Subgroup.relIndex_mul_relIndex _ _ _ d.le hj] at h
  have : ((X.K i).subgroupOf K₀).FiniteIndex := ⟨left_ne_zero_of_mul h⟩
  exact Subgroup.finite_quotient_of_finiteIndex

private theorem tr_step (X : UpperTheory.Gal.G3.Tower B Γ) {i M : X.ι} (hM : M = i) {h x c : Γ} (e : h = x) (hc : c ∈ X.K i)
    (a₁ b₁ a₂ b₂ a₃ b₃) :
    X.tr M i (h * c) a₁ b₁ = X.tr M i 1 a₂ b₂ ≫ X.tr i i x a₃ b₃ := by
  subst hM e
  have h1 := X.tr_mul M M M c h (X.K_le _ _ hc) (fun u hu => mul_mem (mul_mem hc hu) (inv_mem hc)) a₃ b₃ a₁ b₁
  rw [← h1, X.tr_self _ _ _ _ hc, X.tr_self _ _ _ _ (one_mem _)]

private theorem tr_iso (X : UpperTheory.Gal.G3.Tower B Γ) {i M : X.ι} (hM : M = i) (a b) : IsIso (X.tr M i 1 a b) := by
  subst hM
  rw [X.tr_self _ _ _ _ (one_mem _)]
  infer_instance

end Tw

private theorem isIso_desc {C : Type*} [Category C] {I : Type} [Subsingleton I] [Nonempty I] {Y Z : C}
    [HasCoproduct fun _ : I => Y] (f : I → (Y ⟶ Z)) (hf : ∀ i, IsIso (f i)) : IsIso (Sigma.desc f) := by
  let i₀ : I := Classical.arbitrary I
  haveI := hf i₀
  refine ⟨inv (f i₀) ≫ Sigma.ι (fun _ : I => Y) i₀, ?_, ?_⟩
  · refine Sigma.hom_ext _ _ fun b => ?_
    obtain rfl : b = i₀ := Subsingleton.elim _ _
    simp
  · simp

end UpperTheory.TraceConjugationCover

open UpperTheory.TraceConjugationCover in
theorem UpperTheory.tower_covering_of_invariant_finiteEtale_separated :
    PiInv → PiFet → PiSep → SplitOf → KSCover := by
  intro hInv hFet hSep hSplit p _ D G L E _ _ gb w q _ r 𝔴 𝔫 S k T K₀ hLev N c a hNum C hNK J A _ g θ hDeck
  have hK₀ : K₀ ≤ L.KN S.N₀ := by
    have h := hLev
    rw [S.lev] at h
    exact lev_le h
  have hK₁ : K₀ ≤ L.KN 1 := fun x hx => ((hLev x).1 hx).1
  have hd : Dat T.X (T.lev N) K₀ :=
    ⟨by rw [T.K_eq]; exact hNK, fun k hk => (T.Δ_eq _).2 (integ_of_mem (hK₁ hk)),
      fun k hk u hu => by rw [T.K_eq] at hu ⊢; exact conj_mem (hK₁ hk) hu⟩
  have hj : K₀ ≤ T.X.K (T.lev ⟨S.N₀, S.std.three, S.cop⟩) := by rw [T.K_eq]; exact hK₀
  haveI hn : ((T.X.K (T.lev N)).subgroupOf K₀).Normal :=
    ⟨fun u hu k => Subgroup.mem_subgroupOf.2 (by simpa using hd.nrm k k.2 u (Subgroup.mem_subgroupOf.1 hu))⟩
  haveI hfin : Finite (K₀ ⧸ (T.X.K (T.lev N)).subgroupOf K₀) := fin_quot hd hj
  obtain ⟨e, hf, he⟩ := hFet p D G L E gb w q r 𝔴 𝔫 S k T N c a hNum C
  haveI := hf
  haveI := he
  obtain ⟨d, hdim⟩ := S.dim k
  obtain ⟨C', hC'⟩ : ∃ C' : S.Cl (T.M N).univ (c * 1) (((1 : ℕ) : 𝓞 D.F) * a), S.pi T C' = S.pi T C := by
    have : ∀ (c' : ℕ) (a' : 𝓞 D.F), c' = c → a' = a → ∃ C' : S.Cl (T.M N).univ c' a', S.pi T C' = S.pi T C := by
      rintro _ _ rfl rfl
      exact ⟨C, rfl⟩
    exact this _ _ (_root_.mul_one c) (by simp)
  have hinv : ∀ δ, act hd δ ≫ S.pi T C = S.pi T C := fun δ => by
    have := hInv p D G L E gb w q r 𝔴 𝔫 S k T K₀ hLev N N 1 c a (_root_.mul_one _).symm hNum C' C
      (δ⁻¹).out.1 (δ⁻¹).out.2 (hd.mem _ (δ⁻¹).out.2) (hd.nrm _ (δ⁻¹).out.2)
    rw [hC'] at this
    exact this
  have hfst : pullback.lift (S.pi T C) (T.X.q (T.lev N)) e ≫ pullback.fst _ _ = S.pi T C := pullback.lift_fst _ _ e
  have hsnd : pullback.lift (S.pi T C) (T.X.q (T.lev N)) e ≫ pullback.snd _ _ = T.X.q (T.lev N) := pullback.lift_snd _ _ e
  have ha : ∀ δ, act hd δ ≫ pullback.lift (S.pi T C) (T.X.q (T.lev N)) e = pullback.lift (S.pi T C) (T.X.q (T.lev N)) e := by
    intro δ
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hfst]; exact hinv δ
    · rw [Category.assoc, hsnd]; exact act_q hd δ
  have hsep : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (z z' : Sp Ω ⟶ T.X.Z (T.lev N)),
      z ≫ pullback.lift (S.pi T C) (T.X.q (T.lev N)) e = z' ≫ pullback.lift (S.pi T C) (T.X.q (T.lev N)) e →
      ∃! δ, z' = z ≫ act hd δ := by
    intro Ω _ _ z z' h
    have h' : z ≫ S.pi T C = z' ≫ S.pi T C := by
      have h2 := congrArg (· ≫ pullback.fst _ _) h
      simp only [Category.assoc, hfst] at h2
      exact h2
    obtain ⟨u, hu, x, y, e'⟩ := hSep p D G L E gb w q r 𝔴 𝔫 S k T K₀ hLev N c a hNum C Ω z z' h'
    have hz : z' = z ≫ act hd (((⟨u, hu⟩ : K₀)⁻¹ : K₀) : K₀ ⧸ (T.X.K (T.lev N)).subgroupOf K₀) := by
      rw [act_mk]
      exact e'
    exact ⟨_, hz, fun δ' hδ' => act_inj hd hj Ω z _ _ (hδ'.symm.trans hz)⟩
  have hfix : ∀ δ : K₀ ⧸ (T.X.K (T.lev N)).subgroupOf K₀, ∃ j, IsIso ((T.tower N g).s j) ∧
      (T.tower N g).t j = (T.tower N g).s j ≫ act hd δ ∧ θ j = 1 := by
    intro δ
    obtain ⟨j, hK, hM, hh, hθ⟩ := hDeck _ (δ⁻¹).out.2
    have hM' : T.lev (g j).M = T.lev N := by rw [hM]
    have hmem : ∀ x : (g j).K, (x : G.GAf) ∈ T.X.K (T.lev N) := fun x => by
      rw [T.K_eq, ← hK]; exact x.2
    haveI : Subsingleton (g j).I := ⟨fun x y => by
      induction x using QuotientGroup.induction_on with | H x => ?_
      induction y using QuotientGroup.induction_on with | H y => ?_
      refine QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 ?_)
      have := hmem (x⁻¹ * y)
      rwa [T.K_eq] at this⟩
    refine ⟨j, ?_, ?_, hθ⟩
    · exact isIso_desc _ fun _ => tr_iso T.X hM' _ _
    · refine Sigma.hom_ext _ _ fun c => ?_
      have hb : ∀ u ∈ T.X.K (T.lev (g j).M), 1 * u * 1⁻¹ ∈ T.X.K (T.lev N) := fun u hu => by
        rw [T.K_eq] at hu ⊢
        simpa using KN_anti (g j).dvd hu
      have hs : Sigma.ι (fun _ : (g j).I => T.X.Z (T.lev (g j).M)) c ≫ (T.tower N g).s j =
          T.X.tr _ _ 1 (one_mem _) hb := Sigma.ι_desc _ c
      refine (Sigma.ι_desc _ c).trans ?_
      refine (tr_step T.X hM' hh (hmem _) _ _ (one_mem _) hb (hd.mem _ (δ⁻¹).out.2) (hd.nrm _ (δ⁻¹).out.2)).trans ?_
      exact (congrArg (· ≫ act hd δ) hs).symm.trans (Category.assoc _ _ _)
  have hspl := hSplit (T.X.Z (T.lev N)) _ (pullback.lift (S.pi T C) (T.X.q (T.lev N)) e)
    (K₀ ⧸ (T.X.K (T.lev N)).subgroupOf K₀) (act hd) ha hsep
  exact ⟨{
    smooth := SmoothOfRelativeDimension.smooth d _
    proj := S.proj k
    ov := e
    Δ := K₀ ⧸ (T.X.K (T.lev N)).subgroupOf K₀
    a := act hd
    finπ := hf
    etπ := he
    one := act_one hd
    mul := act_mul hd
    spl := hspl
    fix := hfix
    dim := ⟨d, hdim⟩ }⟩

end
