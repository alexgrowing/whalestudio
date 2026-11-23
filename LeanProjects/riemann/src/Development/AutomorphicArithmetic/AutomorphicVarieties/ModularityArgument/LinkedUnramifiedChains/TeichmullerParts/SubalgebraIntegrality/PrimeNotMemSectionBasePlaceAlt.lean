import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.UnramifiedTrivialInertialType
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.Classical
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PlaceBetween
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.CLocConjAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsoSumOfInjectiveEquivariantFamily
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsoSumRestrictionOfLocalComponentUnitary
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsSplitAtOfDecompositionLeRestrictionRange
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.UnderChosenPlaceAndIsSplitAtOfDecompLe

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing Filter
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj)
open UpperTheory.V.HV (Coef)
open UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.Z.Mult (Cp At IsDec CompOf Mult)
open UpperTheory.V.Z.J.D
open scoped Matrix TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.V.Z.J.D.IsotropicFormFiniteness

private theorem isot_of {H W : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ H W) (τ : SmIrr H) (h : IsoSum ρ ⊤ τ) : Isot ρ τ.ρ :=
  h.trans (iSup_le fun f => le_iSup_of_le ⟨f.1, f.2.1⟩ le_rfl)

private theorem isot_at {H M N : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [AddCommGroup M] [Module ℂ M]
    [AddCommGroup N] [Module ℂ N] (ρ : Representation ℂ H M) (ρ' : Representation ℂ H N) (Z : Submodule ℂ N) (τ : SmIrr H)
    (I : Type) [Finite I] (φ : I → M →ₗ[ℂ] N) (hZ : IsoSum ρ' Z τ) (hm : ∀ i y, φ i y ∈ Z)
    (he : ∀ i g y, φ i (ρ g y) = ρ' g (φ i y)) (hi : ∀ y, (∀ i, φ i y = 0) → y = 0) : Isot ρ τ.ρ :=
  isot_of ρ τ (UpperTheory.isoSum_of_injective_equivariant_family H M N ρ ρ' ⊤ Z τ I φ hZ (fun _ _ _ => Submodule.mem_top) (fun i y _ => hm i y)
    (fun i g y _ => he i g y) fun y _ h => hi y h)

private theorem af_tr {Γ Ga Gp : Type} [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) {d : ℕ} (ξ : Gp →* GL (Fin d) ℂ)
    (a : Ga × Gp) (F : Ga × Gp → Fin d → ℂ) (hF : F ∈ X.AF ξ) : (fun g => F (g * a)) ∈ X.AF ξ := fun γ g => by
  have h := hF γ (g * a)
  rw [← mul_assoc] at h
  exact h

private theorem fix_tr {A B M : Type} [Group A] [Group B] [AddCommGroup M] [Module ℂ M] (K : Subgroup A) (a : A × B)
    (h : ∀ k ∈ K, Commute a.1 k) (F : A × B → M)
    (hF : F ∈ fixd ((rtr ℂ (A × B) M).comp (MonoidHom.inl A B)) K) :
    rtr ℂ (A × B) M a F ∈ fixd ((rtr ℂ (A × B) M).comp (MonoidHom.inl A B)) K := fun k hk => by
  funext g
  have h1 : F (g * a * (k, 1)) = F (g * a) := congrFun (hF k hk) (g * a)
  change F (g * (k, 1) * a) = F (g * a)
  rw [← h1, mul_assoc, mul_assoc]
  congr 2
  exact Prod.ext (h k hk).symm.eq (by simp)

variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {s : HidaSetting l L Ω} {n : ℕ}

private theorem l_mem (u : Plc L) :
    ((l : ℕ) : 𝓞 L) ∈ u.asIdeal ↔ ((l : ℕ) : 𝓞 (Lp L)) ∈ (u.under (𝓞 (Lp L))).asIdeal := by
  change _ ↔ algebraMap (𝓞 (Lp L)) (𝓞 L) (l : 𝓞 (Lp L)) ∈ u.asIdeal
  rw [map_natCast]

private theorem SectionSplitPlaces (s : HidaSetting l L Ω) : ((l : ℕ) : 𝓞 (Lp L)) ∉ s.v0.asIdeal := fun h => by
  have hp : ((s.p : ℕ) : 𝓞 (Lp L)) ∈ s.v0.asIdeal := by
    rw [← s.norm_v0_eq_one]
    exact Ideal.absNorm_mem s.v0.asIdeal
  obtain ⟨a, b, hab⟩ : IsCoprime (s.p : 𝓞 (Lp L)) (l : 𝓞 (Lp L)) :=
    ((Nat.coprime_primes s.p_prime Fact.out).2 s.p_ne).cast
  exact s.v0.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (hab ▸ add_mem (Ideal.mul_mem_left _ _ hp) (Ideal.mul_mem_left _ _ h)))

private theorem cmp_at {w : Plc L} (hl : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal) (x : UA L n) :
    UpperTheory.V.Hi.CaseU.cmp n w ((away l L n).rangeRestrict x) = cLoc w x := by
  unfold UpperTheory.V.Hi.CaseU.cmp
  rw [dif_pos hl]
  rfl

private theorem sec_val (hb : Function.Bijective ((toGS n s).comp (GaS n s).subtype)) {a : Ga l L n} (ha : a ∈ GaS n s) :
    secS n s (toGS n s a) = a := by
  unfold secS
  rw [dif_pos hb]
  have h : (MulEquiv.ofBijective _ hb).symm (toGS n s a) = ⟨a, ha⟩ := (MulEquiv.symm_apply_eq _).2 rfl
  change ((MulEquiv.ofBijective _ hb).symm (toGS n s a) : GaS n s).1 = a
  rw [h]

private abbrev JJ (V : s.Lev) (x : UA L n) : Ga l L n × GL' n V :=
  ((away l L n).rangeRestrict x, fun v => cLoc (s.w v.1) x)

private theorem infRep_one (V : s.Lev) (ι : Qbar l ≃+* ℂ) (lam : Wt L l n) {k : UA L n} (hk : k ∈ finU L n) :
    infRep (V := V) ι lam k = 1 := by
  have h1 : ∀ τ : L →+* ℂ, cEmb τ k = 1 := fun τ => by
    change Matrix.GeneralLinearGroup.map (coord τ) (cInf k) = 1
    rw [MonoidHom.mem_ker.1 hk, map_one]
  change PiTensorProduct.mapMonoidHom (fun y : Emb l (fun v : V.frame.Vl => s.w v.1) =>
    GlobalTheory.Branching.sqRep ℂ n (lam y.res) (cEmb (ι.toRingHom.comp y.res) k)) = 1
  simp only [h1, map_one]
  exact map_one _

variable {V : s.Lev} {ι : Qbar l ≃+* ℂ} {lam : Wt L l n} {d : ℕ}
  {e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)}
  {ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ}

private theorem form_fin (hn : 1 ≤ n) (Q : QData V) (c : Coef l) {m : ℕ} (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (hξ : IsBasis ι e ξ) {k : UA L n} (hk : k ∈ finU L n) (F : Ga l L n × GL' n V → Fin d → ℂ)
    (ℓ : Module.Dual ℂ (⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res))) :
    toForm ι e (fun g => F (g * JJ V k)) ℓ = RU L n k (toForm ι e F ℓ) := by
  have h := (formU l L Ω s n hn V Q c m τ₀ ι lam d e ξ hξ _ fun _ => rfl).2.2.1 F ℓ k
  rw [infRep_one V ι lam ((finU L n).inv_mem hk)] at h
  exact h.symm

private def formLin (ι : Qbar l ≃+* ℂ)
    (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) :
    (Ga l L n × GL' n V → Fin d → ℂ) →ₗ[ℂ]
      Module.Dual ℂ (⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) →ₗ[ℂ] (UA L n → ℂ) :=
  LinearMap.mk₂ ℂ (toForm ι e)
    (fun F F' ℓ => funext fun g => by simp only [toForm, Pi.add_apply, map_add])
    (fun a F ℓ => funext fun g => by simp only [toForm, Pi.smul_apply, map_smul])
    (fun _ _ _ => rfl) (fun _ _ _ => rfl)

private theorem span_form {σ : Submodule ℂ (UA L n → ℂ)} {F : Ga l L n × GL' n V → Fin d → ℂ}
    (hF : F ∈ Submodule.span ℂ {F : Ga l L n × GL' n V → Fin d → ℂ | ∀ ℓ, toForm ι e F ℓ ∈ σ}) (ℓ) : toForm ι e F ℓ ∈ σ := by
  have h : Submodule.span ℂ {F : Ga l L n × GL' n V → Fin d → ℂ | ∀ ℓ, toForm ι e F ℓ ∈ σ} ≤
      ⨅ ℓ, σ.comap ((formLin ι e).flip ℓ) :=
    Submodule.span_le.2 fun F hF => (Submodule.mem_iInf _).2 fun ℓ => hF ℓ
  exact (Submodule.mem_iInf _).1 (h hF) ℓ

private theorem vs_stable (hn : 1 ≤ n) (Q : QData V) (c : Coef l) {m : ℕ} (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (hξ : IsBasis ι e ξ) {σ : Submodule ℂ (UA L n → ℂ)} (hσ : IsAutRepU σ)
    (hc : ∀ g, ∀ k ∈ KS n s, Commute (secS n s g) k) (x : GL' n V × GS n s) (F : Ga l L n × GL' n V → Fin d → ℂ)
    (hF : F ∈ VS V ι e ξ Q τ₀ σ) : actS n V d x F ∈ VS V ι e ξ Q τ₀ σ := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := hF
  let a : Ga l L n × GL' n V := (secS n s x.2, x.1)
  have ht : ∀ F' : Ga l L n × GL' n V → Fin d → ℂ, (∀ ℓ, toForm ι e F' ℓ ∈ σ) →
      ∀ ℓ, toForm ι e (rtr ℂ (Ga l L n × GL' n V) (Fin d → ℂ) a F') ℓ ∈ σ := fun F' hF' ℓ => by
    obtain ⟨k, hk⟩ := (formU l L Ω s n hn V Q c m τ₀ ι lam d e ξ hξ _ fun _ => rfl).2.2.2.1 a
    have hk' : a = JJ V k.1 := hk.symm
    have h := form_fin hn Q c τ₀ hξ k.2 F' ℓ
    change toForm ι e (fun g => F' (g * a)) ℓ ∈ σ
    rw [hk', h]
    exact hσ.stable _ _ (hF' ℓ)
  have hs : Submodule.span ℂ {F : Ga l L n × GL' n V → Fin d → ℂ | ∀ ℓ, toForm ι e F ℓ ∈ σ} ≤
      (Submodule.span ℂ {F : Ga l L n × GL' n V → Fin d → ℂ | ∀ ℓ, toForm ι e F ℓ ∈ σ}).comap
        (rtr ℂ (Ga l L n × GL' n V) (Fin d → ℂ) a) :=
    Submodule.span_le.2 fun F' hF' => Submodule.subset_span (ht F' hF')
  exact ⟨⟨af_tr (hset Q τ₀).X ξ a F h1, hs h2⟩, fix_tr (KS n s) a (fun k hk => hc x.2 k hk) F h3⟩

private theorem place (hn : 1 ≤ n) (Q : QData V) (c : Coef l) {m : ℕ} (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (hξ : IsBasis ι e ξ) {σ : Submodule ℂ (UA L n → ℂ)} (hσ : IsAutRepU σ) {w : Plc L} (hsp : IsSplitAt w)
    (τ : SmIrr (GLw n w)) (hτ : Cp σ w τ) (R : Representation ℂ (GLw n w) (VS V ι e ξ Q τ₀ σ))
    (φ : GLw n w →* GL' n V × GS n s) (hR : ∀ g (y : VS V ι e ξ Q τ₀ σ), (R g y).1 = actS n V d (φ g) y.1)
    (hφ : ∀ j : GLw n w →* UA L n, (∀ g, j g ∈ locU n w) → (∀ g, cLoc w (j g) = g) →
      ∀ g, ((secS n s (φ g).2, (φ g).1) : Ga l L n × GL' n V) = JJ V (j g)) : Isot R τ.ρ := by
  obtain ⟨j, h1, h2, -, h3⟩ := (secU l L Ω s n hn w hsp).1
  have hZ := UpperTheory.isoSum_restriction_of_local_component_unitary L n σ hσ w j h1 h2 h3 τ hτ
  have hinj := (formU l L Ω s n hn V Q c m τ₀ ι lam d e ξ hξ _ fun _ => rfl).1
  let b := ((Pi.basisFun ℂ (Fin d)).map e).dualBasis
  refine isot_at R ((RU L n).comp j) σ τ (Fin d)
    (fun i => ((formLin ι e).flip (b i)) ∘ₗ (VS V ι e ξ Q τ₀ σ).subtype) hZ (fun i y => ?_) (fun i g y => ?_) (fun y h0 => ?_)
  · exact span_form y.2.1.2 (b i)
  · change toForm ι e (R g y).1 (b i) = RU L n (j g) (toForm ι e y.1 (b i))
    rw [hR]
    change toForm ι e (fun x => y.1 (x * ((secS n s (φ g).2, (φ g).1) : Ga l L n × GL' n V))) (b i) = _
    rw [hφ j h1 h2 g]
    exact form_fin hn Q c τ₀ hξ (Subgroup.mem_inf.1 (h1 g)).1 y.1 (b i)
  · refine Subtype.ext (hinj y.1 y.2.1.1 fun ℓ => ?_)
    have h : formLin ι e y.1 = 0 := b.ext fun k => h0 k
    exact LinearMap.congr_fun h ℓ

private theorem loc_J (V : s.Lev) (hb : Function.Bijective ((toGS n s).comp (GaS n s).subtype)) {w : Plc L}
    (hw : w.under (𝓞 (Lp L)) ∈ s.St ∨ w.under (𝓞 (Lp L)) = s.v0) {x : UA L n} (hx : x ∈ locU n w) :
    ((secS n s ((fun u : s.St => cLoc (s.w u) x), cLoc (s.w s.v0) x), (1 : GL' n V)) : Ga l L n × GL' n V) = JJ V x := by
  have hu := (UpperTheory.under_chosen_place_and_isSplitAt_of_decomp_le l L Ω s).1
  have hl : ∀ u : Plc L, u.under (𝓞 (Lp L)) ∈ s.St ∨ u.under (𝓞 (Lp L)) = s.v0 → ((l : ℕ) : 𝓞 L) ∉ u.asIdeal := fun u h h' => by
    rcases h with h | h
    · exact s.St_l _ h ((l_mem u).1 h')
    · exact SectionSplitPlaces s (h ▸ (l_mem u).1 h')
  have ha : (away l L n).rangeRestrict x ∈ GaS n s := by
    refine Subgroup.mem_iInf.2 fun u => Subgroup.mem_iInf.2 fun hu' => MonoidHom.mem_ker.2 ?_
    by_cases h : ((l : ℕ) : 𝓞 L) ∈ u.asIdeal
    · unfold UpperTheory.V.Hi.CaseU.cmp
      rw [dif_neg (not_not.2 h)]
      rfl
    · rw [cmp_at h]
      refine GlobalTheory.DefU.LocRet.mem_locU_ne hx fun e => ?_
      rcases hw with hw | hw
      · exact hu'.1 (e ▸ hw)
      · exact hu'.2 (e ▸ hw)
  have ht : toGS n s ((away l L n).rangeRestrict x) = ((fun u : s.St => cLoc (s.w u) x), cLoc (s.w s.v0) x) :=
    Prod.ext (funext fun u => cmp_at (hl _ (Or.inl (by rw [hu]; exact u.2))) x)
      (cmp_at (hl _ (Or.inr (hu _))) x)
  rw [← ht, sec_val hb ha]
  refine Prod.ext rfl (funext fun v => (GlobalTheory.DefU.LocRet.mem_locU_ne hx fun e => ?_).symm)
  have hv : ((l : ℕ) : 𝓞 (Lp L)) ∈ (w.under (𝓞 (Lp L))).asIdeal := by
    rw [← e, hu]
    exact v.2
  exact hl w hw ((l_mem w).2 hv)

end UpperTheory.V.Z.J.D.IsotropicFormFiniteness

open UpperTheory.V.Z.J.D.IsotropicFormFiniteness in
theorem UpperTheory.V.Z.J.D.isotS :
    SecS → SchurGL → BoxIsot → PiIsot → PiIrr → BoxIrr → IsotS := by
  intro hSec hSch hBI hPI hPr hBr l _ L Ω _ _ _ _ _ _ s n hn V hV Q c ι m τ₀ lam d e ξ hξ σ hσ C
  classical
  obtain ⟨hb, hcomm, -⟩ := hSec l L Ω s n hn V hV
  haveI := V.frame.finV
  have hu := (UpperTheory.under_chosen_place_and_isSplitAt_of_decomp_le l L Ω s).1
  let ρ : Representation ℂ (GL' n V × GS n s) (VS V ι e ξ Q τ₀ σ) :=
    (⟨VS V ι e ξ Q τ₀ σ, fun g y hy => vs_stable hn Q c τ₀ hξ hσ hcomm g y hy⟩ : Subrepresentation (actS n V d)).toRepresentation
  refine ⟨ρ, fun _ _ => rfl, ?_⟩
  have aL : ∀ v, AbsIrr (C.l v).ρ := fun v => hSch L n _ (C.l v)
  have aU : ∀ u, AbsIrr (C.u u).ρ := fun u => hSch L n _ (C.u u)
  have aO : AbsIrr C.o.ρ := hSch L n _ C.o
  have pL : AbsIrr C.repL := hPr _ _ _ _ aL
  have pU : AbsIrr (piRep fun u => (C.u u).ρ) := hPr _ _ _ _ aU
  have pS : AbsIrr C.repS := hBr _ _ _ _ _ _ pU aO
  refine hBI _ _ _ _ C.repL C.repS pL pS _ ρ ?_ ?_
  · refine hPI _ _ _ _ aL _ _ fun v => ?_
    have hsp : IsSplitAt (s.w v.1) := UpperTheory.isSplitAt_of_decomposition_le_restriction_range L Ω (s.A v.1) v.1 (s.hA v.1) (s.split v.1 (Or.inl v.2)) _ (hu v.1)
    refine place hn Q c τ₀ hξ hσ hsp (C.l v) (C.hl v) _
      ((MonoidHom.inl _ _).comp (MonoidHom.mulSingle (fun v : V.frame.Vl => GLw n (s.w v.1)) v)) (fun _ _ => rfl)
      fun j h1 h2 g => ?_
    refine Prod.ext ?_ (funext fun u => ?_)
    · change secS n s 1 = _
      rw [map_one]
      refine Subtype.ext (funext fun u => (GlobalTheory.DefU.LocRet.mem_locU_ne (h1 g) fun h => u.2 ?_).symm)
      exact (l_mem u.1).2 (by rw [h, hu]; exact v.2)
    · change Pi.mulSingle (M := fun v : V.frame.Vl => GLw n (s.w v.1)) v g u = cLoc (s.w u.1) (j g)
      by_cases h : u = v
      · subst h
        rw [Pi.mulSingle_eq_same, h2]
      · rw [Pi.mulSingle_eq_of_ne h]
        exact (GlobalTheory.DefU.LocRet.mem_locU_ne (h1 g) fun e => h (Subtype.ext ((hu _).symm.trans (e.trans (hu _))))).symm
  · refine hBI _ _ _ _ _ _ pU aO _ _ ?_ ?_
    · refine hPI _ _ _ _ aU _ _ fun u => ?_
      have hsp : IsSplitAt (s.w u) := UpperTheory.isSplitAt_of_decomposition_le_restriction_range L Ω _ _ (s.hA _) (s.split _ (Or.inr (Or.inl u.2))) _ (hu _)
      refine place hn Q c τ₀ hξ hσ hsp (C.u u) (C.hu u) _
        ((MonoidHom.inr _ _).comp ((MonoidHom.inl _ _).comp (MonoidHom.mulSingle (fun u : s.St => GLw n (s.w u)) u)))
        (fun _ _ => rfl) fun j h1 h2 g => ?_
      refine Eq.trans ?_ (loc_J V hb (Or.inl (by rw [hu]; exact u.2)) (h1 g))
      refine Prod.ext (congrArg (secS n s) (Prod.ext (funext fun u' => ?_) ?_)) rfl
      · change Pi.mulSingle (M := fun u : s.St => GLw n (s.w u)) u g u' = cLoc (s.w u') (j g)
        by_cases h : u' = u
        · subst h
          rw [Pi.mulSingle_eq_same, h2]
        · rw [Pi.mulSingle_eq_of_ne h]
          exact (GlobalTheory.DefU.LocRet.mem_locU_ne (h1 g) fun e => h (Subtype.ext ((hu _).symm.trans (e.trans (hu _))))).symm
      · refine (GlobalTheory.DefU.LocRet.mem_locU_ne (h1 g) fun e => s.v0_St ?_).symm
        have e' : s.v0 = u.1 := (hu _).symm.trans (e.trans (hu _))
        rw [e']
        exact u.2
    · have hsp : IsSplitAt (s.w s.v0) := UpperTheory.isSplitAt_of_decomposition_le_restriction_range L Ω _ _ (s.hA _) (s.split _ (Or.inr (Or.inr rfl))) _ (hu _)
      refine place hn Q c τ₀ hξ hσ hsp C.o C.ho _ ((MonoidHom.inr _ _).comp (MonoidHom.inr _ _)) (fun _ _ => rfl) fun j h1 h2 g => ?_
      refine Eq.trans ?_ (loc_J V hb (Or.inr (hu _)) (h1 g))
      refine Prod.ext (congrArg (secS n s) (Prod.ext (funext fun u' => ?_) (h2 g).symm)) rfl
      refine (GlobalTheory.DefU.LocRet.mem_locU_ne (h1 g) fun e => s.v0_St ?_).symm
      have e' : u'.1 = s.v0 := (hu _).symm.trans (e.trans (hu _))
      rw [← e']
      exact u'.2
