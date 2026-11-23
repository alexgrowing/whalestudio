import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsBaseEqChain
import Development.AbelianVarietyTheory.Definitions.Divisors.FaithfulSMulAlgClosure
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoRestrictPushforwardUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EAComm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeUniquenessOfCovering

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison GlobalTheory.ChainPts
open GlobalTheory.ChainParts
open scoped Classical

noncomputable section

namespace GlobalTheory.ChainParts.LatPart

section General

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {B : Vert.Model O} {Λ : Type} [CommRing Λ]

theorem eA_app (M : AM B Λ) {n : ℕ} (c : Fin n → Γ(B.X, ⊤)) (b : Fin n → Λ) {U : B.X.Opens} (s : Γ(M.V, U))
    (g : Fin n → Γ(B.X, U)) (hg : ∀ k, (M.ρ (b k) : M.V ⟶ M.V).app U s = g k • s) :
    (eA M c b).app U s = (∑ k, resG B.X le_top (c k) * g k) • s := by
  let ev : (M.V ⟶ M.V) →+ Γ(M.V, U) := AddMonoidHom.mk' (fun φ => φ.app U s) fun _ _ => rfl
  refine (map_sum ev _ _).trans ?_
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun k _ => ?_
  change (M.ρ (b k) : M.V ⟶ M.V).app U ((smulHom M.V (c k)).app U s) = _
  rw [smulHom_app_apply, Scheme.Modules.Hom.app_smul, hg, smul_smul]

theorem eA_idem (M : AM B Λ) {r m : ℕ} (hM : GlobalTheory.VB.IsVB M.V r) {n : ℕ} (c : Fin n → Γ(B.X, ⊤)) (b : Fin n → Λ)
    {U : B.X.Opens} (hU : (U : Set B.X).Nonempty) {s : Fin m → Γ(M.V, U)} (hs : GlobalTheory.VB.IsFrame s)
    (h : ∀ i, (eA M c b).app U (s i) = s i ∨ (eA M c b).app U (s i) = 0) :
    eA M c b ≫ (𝟙 M.V - eA M c b) = 0 := by
  rw [Preadditive.comp_sub, Category.comp_id, sub_eq_zero]
  refine LatUniq.hom_ext hM hU hs fun i => ?_
  change _ = (eA M c b).app U ((eA M c b).app U (s i))
  rcases h i with h | h
  · rw [h, h]
  · rw [h, map_zero]

theorem rank_eq {X : Scheme.{0}} {F : X.Modules} {r m : ℕ} (hF : GlobalTheory.VB.IsVB F r) {U : X.Opens}
    (hU : (U : Set X).Nonempty) {s : Fin m → Γ(F, U)} (hs : GlobalTheory.VB.IsFrame s) : r = m := by
  obtain ⟨x, hx⟩ := hU
  rw [← hF.finrank_stalk x, Module.finrank_eq_card_basis (hs.stalkBasis x hx), Fintype.card_fin]

end General

section Model

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

theorem res_const (Z : LocM.Mdl Y i₀) [IsDiscreteValuationRing (Z.i.c.V W)] {B : Vert.Model (Z.i.c.V W)}
    {h : B.X ⟶ Z.X} (hh : h ≫ Z.s = B.str) (a : Fin Z.m) (v : Z.i.c.V W) :
    resG B.X (le_top : h ⁻¹ᵁ (Z.U a).1 ≤ ⊤) (B.const v) = (h.app (Z.U a).1).hom (Z.alg a v) := by
  have e := (isAffineOpen_top (Sp (Z.i.c.V W))).SpecMap_appLE_fromSpec Z.s (Z.U a).2 le_top
  have e' := Z.alg_s a
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp] at e
  have e₂ := Spec.map_injective (e.trans e')
  have e₃ : (Z.s.appLE ⊤ (Z.U a).1 le_top).hom ((Scheme.ΓSpecIso (.of (Z.i.c.V W))).inv.hom v) = Z.alg a v :=
    congrArg (fun φ => φ.hom v) e₂
  rw [← e₃, Vert.Model.const, Vert.Model.const_eq, ← hh]
  have e₄ : Z.s.appLE ⊤ (Z.U a).1 le_top ≫ h.app (Z.U a).1 =
      (h ≫ Z.s).appTop ≫ B.X.presheaf.map (homOfLE (le_top : h ⁻¹ᵁ (Z.U a).1 ≤ ⊤)).op := by
    rw [Scheme.Hom.app_eq_appLE]
    exact Scheme.Hom.appLE_comp_appLE h Z.s ⊤ _ _ _ _
  exact (congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (.of (Z.i.c.V W))).inv.hom v)) e₄).symm

theorem eA_app_const (Z : LocM.Mdl Y i₀) [IsDiscreteValuationRing (Z.i.c.V W)] {B : Vert.Model (Z.i.c.V W)}
    {h : B.X ⟶ Z.X} (hh : h ≫ Z.s = B.str) {Λ : Type} [CommRing Λ] (M : AM B Λ) (a : Fin Z.m)
    (s : Γ(M.V, h ⁻¹ᵁ (Z.U a).1)) {n : ℕ} (cf : Fin n → Z.i.c.V W) (b : Fin n → Λ) (v : Fin n → Z.i.c.V W)
    (hs : ∀ k, (M.ρ (b k) : M.V ⟶ M.V).app _ s = (h.app (Z.U a).1).hom (Z.alg a (v k)) • s) {Q : Prop} [Decidable Q]
    (hv : ∑ k, cf k * v k = if Q then 1 else 0) :
    (eA M (fun k => B.const (cf k)) b).app _ s = if Q then s else 0 := by
  rw [eA_app M _ b s _ hs]
  simp only [← res_const Z hh a, ← map_mul, ← map_sum, hv]
  split_ifs <;> simp

theorem isLatPres_part (Z : LocM.Mdl Y i₀) {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {B : Vert.Model O} {h : B.X ⟶ Z.X} {a₀ : Fin Z.m} (ha : ((h ⁻¹ᵁ (Z.U a₀).1 : B.X.Opens) : Set B.X).Nonempty)
    {Λ : Type} [CommRing Λ] (P : EPres B Λ) {m m' : ℕ} (hr : P.r = m) {x : Fin m → Letter Dw} {d : Bool}
    (s : ∀ a : Fin Z.m, Fin m → Γ(P.E'.V, h ⁻¹ᵁ (Z.U a).1)) (h₁ : IsLat Z h x d d P.E'.V s)
    (h₂ : IsLat Z h x d (!d) P.E.V fun a i => P.ψ.hom.app _ (s a i)) {n : ℕ} (c : Fin n → Γ(B.X, ⊤)) (b : Fin n → Λ)
    (σ : Fin m' → Fin m) (hσ : Function.Injective σ) (hin : ∀ a k, (eA P.E' c b).app _ (s a (σ k)) = s a (σ k))
    (hout : ∀ a i, i ∉ Set.range σ → (eA P.E' c b).app _ (s a i) = 0) (r : ℕ) vb vb' iso :
    IsLatPres Z h (fun k => x (σ k)) d ⟨r, (partF c b).obj P.E, (partF c b).obj P.E', vb, vb', (partF c b).map P.ψ, iso⟩ := by
  have key (M : AM B Λ) (hM : GlobalTheory.VB.IsVB M.V m) (t : ∀ a : Fin Z.m, Fin m → Γ(M.V, h ⁻¹ᵁ (Z.U a).1)) (d' : Bool)
      (ht : IsLat Z h x d d' M.V t) (k₁ : ∀ a k, (eA M c b).app _ (t a (σ k)) = t a (σ k))
      (k₂ : ∀ a i, i ∉ Set.range σ → (eA M c b).app _ (t a i) = 0) :
      ∃ q : M.V ⟶ (partF c b).obj M, q ≫ partι c b M = eA M c b ∧
        IsLat Z h (fun k => x (σ k)) d d' ((partF c b).obj M) fun a k => q.app _ (t a (σ k)) := by
    have hid := eA_idem M hM c b ha (ht.frame a₀) fun i => by
      by_cases hi : i ∈ Set.range σ
      · obtain ⟨k, rfl⟩ := hi
        exact Or.inl (k₁ _ _)
      · exact Or.inr (k₂ _ _ hi)
    have hm : Mono (partι c b M) := inferInstanceAs (Mono (kernel.ι (𝟙 M.V - eA M c b)))
    let q : M.V ⟶ (partF c b).obj M := kernel.lift _ _ hid
    have hq : q ≫ partι c b M = eA M c b := kernel.lift_ι _ _ _
    have hi : partι c b M ≫ eA M c b = partι c b M := by
      have := kernel.condition (𝟙 M.V - eA M c b)
      rw [Preadditive.comp_sub, Category.comp_id, sub_eq_zero] at this
      exact this.symm
    have hiq : partι c b M ≫ q = 𝟙 _ := by
      rw [← cancel_mono (partι c b M), Category.assoc, hq, hi, Category.id_comp]
    have happ {U : B.X.Opens} (u : Γ(M.V, U)) : (partι c b M).app U (q.app U u) = (eA M c b).app U u :=
      congrArg (fun φ => Scheme.Modules.Hom.app φ U u) hq
    refine ⟨q, hq, SummandLat.isLat_summand Z h (partι c b M) q hiq σ hσ hM x d d' t ht
      (fun a k => (happ _).trans (k₁ a k)) fun a i hi' => ?_⟩
    have e : q.app _ (t a i) = q.app _ ((partι c b M).app _ (q.app _ (t a i))) :=
      (congrArg (fun φ => Scheme.Modules.Hom.app φ _ (q.app _ (t a i))) hiq).symm
    rw [e, happ, k₂ a i hi', map_zero]
  have comm {U : B.X.Opens} (u : Γ(P.E'.V, U)) :
      (eA P.E c b).app U (P.ψ.hom.app U u) = P.ψ.hom.app U ((eA P.E' c b).app U u) :=
    (congrArg (fun φ => Scheme.Modules.Hom.app φ U u) (eA_comm P.ψ c b)).symm
  obtain ⟨q', hq', k'⟩ := key P.E' (hr ▸ P.vb') s d h₁ hin hout
  obtain ⟨q, hq, k⟩ := key P.E (hr ▸ P.vb) _ (!d) h₂ (fun a k => by rw [comm, hin])
    fun a i hi => by rw [comm, hout a i hi, map_zero]
  have hm : Mono (partι c b P.E) := inferInstanceAs (Mono (kernel.ι (𝟙 P.E.V - eA P.E c b)))
  have nat : (partF c b).map P.ψ ≫ partι c b P.E = partι c b P.E' ≫ P.ψ.hom := kernel.lift_ι _ _ _
  have e : q' ≫ (partF c b).map P.ψ = P.ψ.hom ≫ q := by
    rw [← cancel_mono (partι c b P.E), Category.assoc, nat, ← Category.assoc, hq', Category.assoc, hq, eA_comm]
  refine ⟨rank_eq vb' ha (k'.frame a₀), fun a k => q'.app _ (s a (σ k)), k', ?_⟩
  have e' : (fun (a : Fin Z.m) (k : Fin m') => ((partF c b).map P.ψ).app _ (q'.app _ (s a (σ k)))) =
      fun a k => q.app _ (P.ψ.hom.app _ (s a (σ k))) :=
    funext fun a => funext fun k => congrArg (fun φ => Scheme.Modules.Hom.app φ _ (s a (σ k))) e
  exact e' ▸ k

end Model

theorem exists_xLie {D : D7} {A : Amb D} {N j : ℕ} (S : Sig A N j) {p : ℕ} [Fact p.Prime] (jc : KW p →+* ℂ) (τ : Emb D p)
    (y : Letter S.Dw) (h : y.1 = jc.comp τ) : ∃ k, xLie S jc τ k = y := by
  obtain ⟨t, k⟩ := y
  subst h
  exact ⟨k.cast (mult_comp S jc τ), rfl⟩

theorem isLatPres_xLie : ∀ {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ} [Fact p.Prime] {hp : p.Prime} {W : ValuationSubring ℂ} {hW : (p : ℂ) ∈ W.nonunits} (z : AdmAt S κ hp hW) (jc : KW p →+* ℂ), haveI := isDiscreteValuationRing_V z.Z.i.c hp hW
    haveI := charP_residueField_of_mem_nonunits z.Z.i.c hp hW
    ∀ (c : (nmodel z.Z).Comp) (B : Vert.Model (z.Z.i.c.V W)) (f : Vert.Model.Hom B ((nmodel z.Z).comp c)) (n : ℕ)
      (b : Fin n → 𝓞 D.host.E) (ev : Emb D p → (𝓞 D.host.E →+* z.Z.i.c.V W)) (cf : Emb D p → Fin n → z.Z.i.c.V W),
      (∀ σ x, ((ev σ x : z.Z.i.c.V W) : z.Z.i.c.F) = embK z.Z.i.c (jc.comp σ) x) →
      (∀ σ' : D.host.E →+* ℂ, ∃ σ : Emb D p, σ' = jc.comp σ) →
      (∀ τ σ : Emb D p, ∑ k, cf τ k * ev σ (b k) = if σ = τ then 1 else 0) →
      ∀ P : EPres B (𝓞 D.host.E), IsEqLatPres z.Z (f.f ≫ (nmodel z.Z).compι c) (xAll S) false P →
      ∀ (τ : Emb D p) (r : ℕ) vb vb' iso, IsLatPres z.Z (f.f ≫ (nmodel z.Z).compι c) (xLie S jc τ) false
        ⟨r, (partF (fun k => B.const (cf τ k)) b).obj P.E, (partF (fun k => B.const (cf τ k)) b).obj P.E', vb, vb',
          (partF (fun k => B.const (cf τ k)) b).map P.ψ, iso⟩ := by
  intro D A N j S κ p _ hp W hW z jc
  intro c B f n b ev cf hev hall hcf P hP τ r vb vb' iso
  haveI := isDiscreteValuationRing_V z.Z.i.c hp hW
  obtain ⟨hr, s, h₁, h₂, h₃⟩ := hP
  obtain ⟨a₀, ha₀⟩ := GlobalTheory.TestPts.exists_chart_of_maximal _ (GlobalTheory.TestPts.mem_opn_comp hp hW f) (η := genericPoint B.X)
    fun y hy => (hy.antisymm ((genericPoint_spec B.X).specializes (Set.mem_univ y))).eq
  have hh : (f.f ≫ (nmodel z.Z).compι c) ≫ z.Z.s = B.str := by
    rw [Category.assoc]
    exact f.comp_str
  choose σ hσ using fun k => (xAll_bijective S).2 (xLie S jc τ k)
  have act (a : Fin z.Z.m) (i : Fin (D.R.f * N)) (σ₀ : Emb D p) (h₀ : (xAll S i).1 = jc.comp σ₀) :
      (eA P.E' (fun k => B.const (cf τ k)) b).app _ (s a i) = if σ₀ = τ then s a i else 0 := by
    refine eA_app_const z.Z hh P.E' a (s a i) (cf τ) b (fun k => ev σ₀ (b k)) (fun k => ?_) (hcf τ σ₀)
    have e : embK z.Z.i.c (xAll S i).1 (b k) = (ev σ₀ (b k) : z.Z.i.c.F) :=
      (congrArg (fun t => embK z.Z.i.c t (b k)) h₀).trans (hev σ₀ (b k)).symm
    exact (h₃ a i (b k)).trans (congrArg (fun u => ((f.f ≫ (nmodel z.Z).compι c).app (z.Z.U a).1).hom (z.Z.alg a u) • s a i) e)
  have hx : xLie S jc τ = fun k => xAll S (σ k) := funext fun k => (hσ k).symm
  rw [hx]
  refine isLatPres_part z.Z ⟨_, ha₀⟩ P hr s h₁ h₂ _ b σ (fun k l e => (xLie_initial S jc τ).1 ?_) (fun a k => ?_)
    (fun a i hi => ?_) r vb vb' iso
  · exact (hσ k).symm.trans ((congrArg (xAll S) e).trans (hσ l))
  · exact (act a _ τ (congrArg Sigma.fst (hσ k))).trans (if_pos rfl)
  · refine (hall (xAll S i).1).elim fun σ₀ h₀ => (act a i σ₀ h₀).trans (if_neg fun e => ?_)
    exact (exists_xLie S jc τ (xAll S i) (h₀.trans (congrArg jc.comp e))).elim fun k hk =>
      hi ⟨k, (xAll_bijective S).1 ((hσ k).trans hk)⟩

end GlobalTheory.ChainParts.LatPart

end
