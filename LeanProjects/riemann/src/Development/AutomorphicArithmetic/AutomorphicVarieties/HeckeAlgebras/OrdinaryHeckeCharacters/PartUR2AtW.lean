import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.Classical
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PlaceBetween
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.CLocConjAlt
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

private theorem w_under {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (v : Plc (Lp L)) : (s.w v).under (𝓞 (Lp L)) = v := by
  ext x
  exact (s.hw v (algebraMap (𝓞 (Lp L)) (𝓞 L) x)).symm.trans (s.hA v x)

private theorem cLoc_ne {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {w u : Plc L}
    {x : UA L n} (hx : x ∈ locU n w) (hu : u.under (𝓞 (Lp L)) ≠ w.under (𝓞 (Lp L))) : cLoc u x = 1 :=
  MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hx).2 u) hu)

private theorem cmp_of {l : ℕ} [Fact l.Prime] {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {w : Plc L}
    (h : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal) (x : UA L n) : cmp n w ((away l L n).rangeRestrict x) = cLoc w x := by
  unfold CaseU.cmp
  rw [dif_pos h]
  rfl

private theorem cmp_loc {l : ℕ} [Fact l.Prime] {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {w u : Plc L}
    {x : UA L n} (hx : x ∈ locU n w) (hu : u.under (𝓞 (Lp L)) ≠ w.under (𝓞 (Lp L))) :
    cmp n u ((away l L n).rangeRestrict x) = 1 := by
  by_cases h : ((l : ℕ) : 𝓞 L) ∉ u.asIdeal
  · rw [cmp_of h]
    exact cLoc_ne hx hu
  · unfold CaseU.cmp
    rw [dif_neg h]
    rfl

section

variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
  [IsAlgClosure L Ω] (s : HidaSetting l L Ω) {n : ℕ}

private theorem sec_eq (hn : 1 ≤ n) {w : Plc L} (hw : IsSplitAt w) (hS : w.under (𝓞 (Lp L)) ∉ s.S) {x : UA L n}
    (hx : x ∈ locU n w) : ((sec n s w (cLoc w x) : Ub n s) : Ga l L n) = (away l L n).rangeRestrict x := by
  obtain ⟨hb, h1, h2⟩ := (secU l L Ω s n hn w hw).2 hS
  have hl : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal := fun h => hS <| Or.inl <| by
    change algebraMap (𝓞 (Lp L)) (𝓞 L) (l : 𝓞 (Lp L)) ∈ w.asIdeal
    rwa [map_natCast]
  have hU : (away l L n).rangeRestrict x ∈ Ub n s := by
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_iInf.2 fun u => ?_, ?_⟩
    · rw [Subgroup.mem_comap, cmp_loc hx (by
        rw [w_under]
        exact fun h => hS (Or.inr (Or.inl (h ▸ u.2))))]
      exact one_mem _
    · rw [Subgroup.mem_comap, cmp_loc hx (by
        rw [w_under]
        exact fun h => hS (Or.inr (Or.inr h.symm)))]
      exact one_mem _
  have hA : (⟨_, hU⟩ : Ub n s) ∈ locA n s w := Subgroup.mem_iInf.2 fun u => Subgroup.mem_iInf.2 fun hu =>
    MonoidHom.mem_ker.2 (cmp_loc hx hu)
  have h3 : (⟨_, h2 (cLoc w x)⟩ : locA n s w) = ⟨_, hA⟩ := hb.1 ((h1 _).trans (cmp_of hl x).symm)
  exact congrArg (fun y : locA n s w => (y.1 : Ga l L n)) h3

private theorem toKT_sec (hn : 1 ≤ n) {w : Plc L} (hw : IsSplitAt w) (hS : w.under (𝓞 (Lp L)) ∉ s.S) (g : GLw n w) :
    toKT n s (sec n s w g) = 1 := by
  obtain ⟨-, -, h2⟩ := (secU l L Ω s n hn w hw).2 hS
  refine Subtype.ext (funext fun u => ?_)
  exact MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (h2 g) (s.w u)) (by
    rw [w_under]
    exact fun h => hS (Or.inr (Or.inl (h ▸ u.2)))))

private theorem infRep_fin {s : HidaSetting l L Ω} (V : s.Lev) (ι : Qbar l ≃+* ℂ) (lam : Wt L l n) {k : UA L n}
    (hk : k ∈ finU L n) : infRep (V := V) ι lam k = 1 := by
  have h1 : ∀ τ : L →+* ℂ, cEmb τ k = 1 := fun τ => by
    change Matrix.GeneralLinearGroup.map (coord τ) (cInf k) = 1
    rw [MonoidHom.mem_ker.1 hk, map_one]
  change PiTensorProduct.mapMonoidHom (fun y : Emb l (fun v : V.frame.Vl => s.w v.1) =>
    GlobalTheory.Branching.sqRep ℂ n (lam y.res) (cEmb (ι.toRingHom.comp y.res) k)) = 1
  simp only [h1, map_one]
  exact map_one _

end

private theorem raF_one {Γ Ga Gp : Type} [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) {d m : ℕ}
    (τ : X.Ub →* GL (Fin m) ℂ) (u : X.Ub) (hu : τ u = 1) (F : Fin m → X.Fn ℂ d) (i : Fin m) (x : Ga × Gp) :
    X.raF d τ u F i x = F i (x * ((u : Ga), 1)) := by
  funext k
  change X.ra τ u (fun g j => F j g k) x i = _
  rw [X.ra_apply, hu, Units.val_one, Matrix.one_mulVec]

theorem UpperTheory.V.Hi.partUR2AtW :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l) (ι : Qbar l ≃+* ℂ) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (lam : Wt L l n) (d : ℕ) (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ), IsBasis ι e ξ →
    ∀ w : Plc L, IsSplitAt w → w.under (𝓞 (Lp L)) ∉ s.S → ∀ (j : GLw n w →* UA L n), (∀ g, j g ∈ locU n w) → (∀ g, cLoc w (j g) = g) →
    ∀ (F : Fin m → (hset Q τ₀).X.Fn ℂ d) (g : GLw n w) (i : Fin m) ℓ, toForm ι e ((hset Q τ₀).atW ι d w g F i) ℓ = RU L n (j g) (toForm ι e (F i) ℓ) := by
  intro l _ L Ω _ _ _ _ _ _ s n hn V Q c ι m τ₀ lam d e ξ _ w hw hS j hj1 hj2 F g i ℓ
  funext x
  have h1 : (hset Q τ₀).τC ι (sec n s w g) = 1 := by
    change Matrix.GeneralLinearGroup.map (ι.toRingHom.comp (algebraMap c.O (Qbar l))) (τ₀ (toKT n s (sec n s w g))) = 1
    rw [toKT_sec s hn hw hS, map_one, map_one]
  have h2 : ((sec n s w g : Ub n s) : Ga l L n) = (away l L n).rangeRestrict (j g) := by
    have := sec_eq s hn hw hS (hj1 g)
    rwa [hj2] at this
  have h3 : ∀ v : V.frame.Vl, cLoc (s.w v.1) (j g) = 1 := fun v => cLoc_ne (hj1 g) (by
    rw [w_under]
    exact fun h => hS (Or.inl (h ▸ v.2)))
  have h4 : infRep (V := V) ι lam (x * j g)⁻¹ = infRep (V := V) ι lam x⁻¹ := by
    rw [mul_inv_rev, map_mul, infRep_fin V ι lam ((finU L n).inv_mem (Subgroup.mem_inf.1 (hj1 g)).1), one_mul]
  have h5 : (show Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) from
        ((away l L n).rangeRestrict x, fun v : V.frame.Vl => cLoc (s.w v.1) x)) *
      (show Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) from (((sec n s w g : Ub n s) : Ga l L n), 1)) =
      ((away l L n).rangeRestrict (x * j g), fun v : V.frame.Vl => cLoc (s.w v.1) (x * j g)) := by
    refine Prod.ext ?_ (funext fun v => ?_)
    · change (away l L n).rangeRestrict x * ((sec n s w g : Ub n s) : Ga l L n) = (away l L n).rangeRestrict (x * j g)
      rw [h2, map_mul]
    · change cLoc (s.w v.1) x * 1 = cLoc (s.w v.1) (x * j g)
      rw [map_mul, h3]
  have h6 := (raF_one (hset Q τ₀).X ((hset Q τ₀).τC ι) (sec n s w g) h1 F i
    ((away l L n).rangeRestrict x, fun v : V.frame.Vl => cLoc (s.w v.1) x)).trans (congrArg (F i) h5)
  change _ = ℓ (infRep ι lam (x * j g)⁻¹ (e _))
  rw [h4]
  exact congrArg (fun y => ℓ (infRep (V := V) ι lam x⁻¹ (e y))) h6
