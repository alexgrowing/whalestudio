import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.NeTeichEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.UnitaryHeckeData
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
private theorem neu_comm {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {w : Plc L} {j : GLw n w →* UA L n}
    (hj : ∀ x ∈ locU n w, x = j (cLoc w x)) {g y : UA L n} (hg : cLoc w g = 1) (hy : y ∈ locU n w) : Commute g y := by
  have h1 : (GlobalTheory.DefU.LocRet.ret w n g : UA L n) = 1 := by
    rw [hj _ (GlobalTheory.DefU.LocRet.ret w n g).2]
    have : cLoc w (GlobalTheory.DefU.LocRet.ret w n g : UA L n) = cLoc w g := GlobalTheory.DefU.LocRet.localProj_unitaryAdelicLocalRetractionEnd_of_under_eq rfl g
    rw [this, hg, map_one]
  have h2 := GlobalTheory.DefU.LocRet.commute_ret g ⟨y, hy⟩
  rwa [h1, inv_one, one_mul] at h2
private theorem ne_J {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {St : Type} [Fintype St] [DecidableEq St]
    {wt : St → Plc L} (hinj : Function.Injective fun u => (wt u).under (𝓞 (Lp L))) (j : ∀ u, GLw n (wt u) →* UA L n)
    (h1 : ∀ u g, j u g ∈ locU n (wt u)) (h2 : ∀ u g, cLoc (wt u) (j u g) = g) (h3 : ∀ u, ∀ x ∈ locU n (wt u), x = j u (cLoc (wt u) x)) :
    ∃ J : GV n wt →* UA L n, (∀ u g, J (Pi.mulSingle u g) = j u g) ∧ (∀ g, J g ∈ GlobalTheory.UnitaryBC.finU L n) ∧
      (∀ g u, cLoc (wt u) (J g) = g u) ∧
      (∀ g (v : Plc L), (∀ u, v.under (𝓞 (Lp L)) ≠ (wt u).under (𝓞 (Lp L))) → cLoc v (J g) = 1) ∧
      ∀ g k, (∀ u, cLoc (wt u) k = 1) → Commute k (J g) := by
  have h4 : ∀ u g (v : Plc L), v.under (𝓞 (Lp L)) ≠ (wt u).under (𝓞 (Lp L)) → cLoc v (j u g) = 1 := fun u g v hv =>
    GlobalTheory.DefU.LocRet.mem_locU_ne (h1 u g) hv
  have hc : Pairwise fun a b => ∀ x y, Commute (j a x) (j b y) := fun a b hab x y =>
    neu_comm (h3 b) (h4 a x _ fun e => hab (hinj e).symm) (h1 b y)
  let J := MonoidHom.noncommPiCoprod j hc
  have hJ : ∀ u g, J (Pi.mulSingle u g) = j u g := fun u g => MonoidHom.noncommPiCoprod_mulSingle j u g
  have key : ∀ P : Subgroup (UA L n), (∀ u g, j u g ∈ P) → ∀ g, J g ∈ P := fun P hP g => by
    have : J.range ≤ P := by
      rw [MonoidHom.noncommPiCoprod_range]
      exact iSup_le fun u => by rintro _ ⟨g, rfl⟩; exact hP u g
    exact this ⟨g, rfl⟩
  refine ⟨J, hJ, key _ fun u g => (h1 u g).1, fun g u => ?_, fun g v hv => key (cLoc v).ker (fun u g => h4 u g v (hv u)) g,
    fun g k hk => ?_⟩
  · have : (cLoc (wt u)).comp J = Pi.evalMonoidHom (fun u => GLw n (wt u)) u := MonoidHom.pi_ext fun i x => by
      rw [MonoidHom.comp_apply, hJ, Pi.evalMonoidHom_apply]
      by_cases h : u = i
      · subst h
        rw [h2, Pi.mulSingle_eq_same]
      · rw [Pi.mulSingle_eq_of_ne h]
        exact h4 i x _ fun e => h (hinj e)
    exact DFunLike.congr_fun this g
  · exact (Subgroup.mem_centralizer_singleton_iff.1
      (key (Subgroup.centralizer {k}) (fun u g => Subgroup.mem_centralizer_singleton_iff.2
        (neu_comm (h3 u) (hk u) (h1 u g)).symm.eq) g)).symm
private theorem ne_iso {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {w : Plc L} {j : GLw n w →* UA L n}
    (h1 : ∀ g, j g ∈ locU n w) (h2 : ∀ g, cLoc w (j g) = g) (h3 : ∀ x ∈ locU n w, x = j (cLoc w x))
    {σ : Submodule ℂ (UA L n → ℂ)} (hσ : IsAutRepU σ) (τ : SmIrr (GLw n w))
    (hτ : IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ)
    (M : Submodule ℂ (UA L n → ℂ)) (hM : M ≤ σ) (ρ : Representation ℂ (GLw n w) M) (hρ : ∀ g y, (ρ g y : UA L n → ℂ) = RU L n (j g) y) :
    IsoSum ρ ⊤ τ := by
  let π : GlobalTheory.DefU.AutSub L n := ⟨σ, hσ⟩
  obtain ⟨-, f, hf0, hfm, hf⟩ := hτ
  let F : Representation.IntertwiningMap τ.ρ (π.rep.comp j) :=
    ⟨f.codRestrict _ hfm, fun x => LinearMap.ext fun v => Subtype.ext (by
      have := hf ⟨j x, h1 x⟩ v
      rwa [show ((cLoc w).comp (locU n w).subtype) ⟨j x, h1 x⟩ = x from h2 x] at this)⟩
  have hF0 : F ≠ 0 := fun h => hf0 (LinearMap.ext fun v => congrArg Subtype.val (DFunLike.congr_fun h v))
  have htop := (GlobalTheory.CuspRep.CompUniq.isotypic (UA L n) (GLw n w) π.V τ.V τ.V π.rep j τ.ρ τ.ρ π.isIrreducible_rep τ.irred τ.irred
    (fun g => ⟨cLoc w g, fun y => neu_comm h3 (by rw [map_mul, map_inv, h2, inv_mul_cancel]) (h1 y)⟩) F hF0).1
  have h5 := UpperTheory.isotypic_of_jointly_injective_into_isotypic _ _ _ τ.ρ (π.rep.comp j) τ.irred (by
    refine top_le_iff.1 (htop.ge.trans (iSup_le fun f => ?_))
    exact le_iSup_of_le ⟨f.toLinearMap, fun g v => LinearMap.congr_fun (f.isIntertwining' g) v⟩ le_rfl)
    M ρ Unit (fun _ => Submodule.inclusion hM) (fun _ g y => Subtype.ext (hρ g y))
    (fun y hy => Submodule.inclusion_injective hM ((hy ()).trans (map_zero _).symm))
  refine h5.ge.trans (iSup_le fun f => ?_)
  exact le_iSup_of_le ⟨f.1, f.2, le_top⟩ le_rfl
private theorem ne_type {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {n m : ℕ}
    {St : Type} [Finite St] {wt : St → Plc L} {At : St → ValuationSubring Ω} (ht : ∀ u, IsPlaceOver (At u) (wt u))
    (hinj : Function.Injective fun u => (wt u).under (𝓞 (Lp L))) (j : ∀ u, GLw n (wt u) →* UA L n)
    (h1 : ∀ u g, j u g ∈ locU n (wt u)) (h2 : ∀ u g, cLoc (wt u) (j u g) = g) (h3 : ∀ u, ∀ x ∈ locU n (wt u), x = j u (cLoc (wt u) x))
    (τ₀ : KT n wt →* GL (Fin m) ℂ) (χ : ∀ u, Fin n → Ine (F := L) (At u) →* ℂˣ) (hT : _root_.UpperTheory.V.Hi.IsTypeAlt ht τ₀ χ)
    {σ : Submodule ℂ (UA L n → ℂ)} (hσ : IsAutRepU σ) (τ : ∀ u, SmIrr (GLw n (wt u)))
    (hτ : ∀ u, IsCompAlong σ (locU n (wt u)) ((cLoc (wt u)).comp (locU n (wt u)).subtype) (τ u).ρ)
    (hwd : ∀ u rc, _root_.UpperTheory.Zero.LLC.IsRecT (ht u) rc → IsTypeWD (ht u) (χ u) (rc (algNorm (τ u))))
    (K : Subgroup (UA L n)) (hK : ∀ k ∈ K, ∀ u, cLoc (wt u) k = 1) (h0 : σ ⊓ fixd (RU L n) K ≠ ⊥) :
    ∃ J : GV n wt →* UA L n, (∀ g, J g ∈ GlobalTheory.UnitaryBC.finU L n) ∧ (∀ g u, cLoc (wt u) (J g) = g u) ∧
      (∀ g (v : Plc L), (∀ u, v.under (𝓞 (Lp L)) ≠ (wt u).under (𝓞 (Lp L))) → cLoc v (J g) = 1) ∧
      ∃ F : Fin m → UA L n → ℂ, F ≠ 0 ∧ (∀ i, F i ∈ σ ⊓ fixd (RU L n) K) ∧
        ∀ (k : KT n wt) i, ∑ a, τ₀ k i a • RU L n (J k) (F a) = F i := by
  classical
  letI := Fintype.ofFinite St
  obtain ⟨J, hJ, j1, j2, j3, j4⟩ := ne_J hinj j h1 h2 h3
  let M := σ ⊓ fixd (RU L n) K
  have hst : ∀ g, ∀ φ ∈ M, ((RU L n).comp J) g φ ∈ M := fun g φ hφ => ⟨hσ.stable _ _ hφ.1, fun k hk => by
    change RU L n k (RU L n (J g) φ) = RU L n (J g) φ
    rw [GlobalTheory.DefU.RU_RU, (j4 g k (hK k hk)).eq, ← GlobalTheory.DefU.RU_RU, hφ.2 k hk]⟩
  haveI : Nontrivial M := Submodule.nontrivial_iff_ne_bot.2 h0
  let ρ : Representation ℂ (GV n wt) M := GlobalTheory.PRep.sub ((RU L n).comp J) M hst
  obtain ⟨F, hF0, hF⟩ := (hT.2 M ρ τ fun u => ne_iso (h1 u) (h2 u) (h3 u) hσ (τ u) (hτ u) M inf_le_left _ fun g y => by
    change RU L n (J (Pi.mulSingle u g)) y = _
    rw [hJ]).2 hwd
  refine ⟨J, j1, j2, j3, fun i => F i, fun e => hF0 (funext fun i => Subtype.ext (congrFun e i)), fun i => (F i).2, fun k i => ?_⟩
  have := congrArg M.subtype (hF k i)
  rw [map_sum] at this
  exact this
private theorem ne_teich_ex (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O]
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] [CharP (ResidueField O) l] :
    ∃ τ : ResidueField O →* O, ∀ x, residue O (τ x) = x := by
  haveI : CharP (O ⧸ maximalIdeal O) l := inferInstanceAs (CharP (ResidueField O) l)
  haveI : PerfectRing (ResidueField O) l := inferInstance
  let j : ResidueField O →+* Perfection (O ⧸ maximalIdeal O) l :=
    Perfection.lift l (ResidueField O) (O ⧸ maximalIdeal O) (RingHom.id (ResidueField O))
  have hj : ∀ x, Perfection.coeff (O ⧸ maximalIdeal O) l 0 (j x) = x := fun x => by
    have := (Perfection.lift l (ResidueField O) (O ⧸ maximalIdeal O)).symm_apply_apply (RingHom.id (ResidueField O))
    exact RingHom.congr_fun this x
  refine ⟨(Perfection.teichmuller l (maximalIdeal O)).comp j, fun x => ?_⟩
  exact (Perfection.mk_teichmuller (j x)).trans (hj x)
private theorem ne_isTeich {l : ℕ} [hl : Fact l.Prime] {F : W.GFrame l} (c : Coef l) {n : ℕ} (r : Resid F c.O n) :
    ∃ t, r.IsTeich t := by
  obtain ⟨hc, hfin, hlm, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
  haveI : Finite (ResidueField c.O) := hfin
  haveI : CharP (ResidueField c.O) l := by
    refine (CharP.charP_iff_prime_eq_zero hl.out).2 ?_
    rw [← map_natCast (residue c.O), residue_eq_zero_iff]
    exact hlm
  obtain ⟨τ, hτ⟩ := ne_teich_ex l c.O
  refine ⟨fun i => (Units.map τ).comp (r.chib i), fun i g => ⟨hτ _, ?_⟩⟩
  rw [MonoidHom.comp_apply, ← map_pow, ← Nat.card_units, pow_card_eq_one', map_one]
private theorem ne_notMem {l : ℕ} {L : Type} [Field L] [NumberField L] [IsCMField L] {u : Plc L}
    (h : ((l : ℕ) : 𝓞 (Lp L)) ∉ (u.under (𝓞 (Lp L))).asIdeal) : ((l : ℕ) : 𝓞 L) ∉ u.asIdeal := fun h' => h <| by
  change algebraMap (𝓞 (Lp L)) (𝓞 L) (l : 𝓞 (Lp L)) ∈ u.asIdeal
  rwa [map_natCast]
private theorem ne_cmp {l : ℕ} [Fact l.Prime] {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {w : Plc L}
    (h : ((l : ℕ) : 𝓞 (Lp L)) ∉ (w.under (𝓞 (Lp L))).asIdeal) (x : UA L n) :
    cmp n w ((away l L n).rangeRestrict x) = cLoc w x := by
  unfold CaseU.cmp
  rw [dif_pos (ne_notMem h)]
  rfl
section
variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {s : HidaSetting l L Ω} (n : ℕ) {V : s.Lev} (Q : QData V)
private noncomputable def neK : Subgroup (UA L n) :=
  GlobalTheory.UnitaryBC.finU L n ⊓
    (⨅ (u : Plc L) (_ : u.under (𝓞 (Lp L)) ∉ V.S'), (KO (u.adicCompletion L) (Fin n)).comap (cLoc u)) ⊓
    (Kc _ n 1).comap (cLoc (s.w s.v0)) ⊓ (⨅ v : V.frame.Vl, (cLoc (s.w v.1)).ker) ⊓ (⨅ u : s.St, (cLoc (s.w u)).ker) ⊓
    ⨅ q : Q.Q, (cLoc (Q.wq q)).ker
variable {n Q}
private theorem mem_neK {k : UA L n} : k ∈ neK n Q ↔ k ∈ GlobalTheory.UnitaryBC.finU L n ∧
    (∀ u : Plc L, u.under (𝓞 (Lp L)) ∉ V.S' → cLoc u k ∈ KO (u.adicCompletion L) (Fin n)) ∧ cLoc (s.w s.v0) k ∈ Kc _ n 1 ∧
    (∀ v : V.frame.Vl, cLoc (s.w v.1) k = 1) ∧ (∀ u : s.St, cLoc (s.w u) k = 1) ∧ ∀ q : Q.Q, cLoc (Q.wq q) k = 1 := by
  simp only [neK, Subgroup.mem_inf, Subgroup.mem_iInf, Subgroup.mem_comap, MonoidHom.mem_ker, and_assoc]
private theorem ne_dec (J : GV n (wt s) →* UA L n) (j1 : ∀ g, J g ∈ GlobalTheory.UnitaryBC.finU L n) (j2 : ∀ g u, cLoc (wt s u) (J g) = g u)
    (j3 : ∀ g (v : Plc L), (∀ u, v.under (𝓞 (Lp L)) ≠ (wt s u).under (𝓞 (Lp L))) → cLoc v (J g) = 1)
    (u : Ub n s) (hu : u ∈ UQ n Q) (x : UA L n) (hx : x ∈ GlobalTheory.UnitaryBC.finU L n) (h1 : (away l L n).rangeRestrict x = u)
    (h2 : ∀ v : V.frame.Vl, cLoc (s.w v.1) x = 1) : (J (toKT n s u))⁻¹ * x ∈ neK n Q := by
  have hw := (UpperTheory.under_chosen_place_and_isSplitAt_of_decomp_le l L Ω s).1
  have j4 : ∀ v : Plc L, v.under (𝓞 (Lp L)) ∉ s.St → cLoc v ((J (toKT n s u))⁻¹ * x) = cLoc v x := fun v hv => by
    rw [map_mul, map_inv, j3 _ v fun a e => hv (by rw [e, hw]; exact a.2), inv_one, one_mul]
  have hc : ∀ v : Plc L, ((l : ℕ) : 𝓞 (Lp L)) ∉ (v.under (𝓞 (Lp L))).asIdeal → cLoc v x = cmp n v (u : Ga l L n) := fun v hv => by
    rw [← h1, ne_cmp hv]
  obtain ⟨hu1, hu2⟩ := Subgroup.mem_inf.1 hu
  refine mem_neK.2 ⟨mul_mem (inv_mem (j1 _)) hx, fun v hv => ?_, ?_, fun v => ?_, fun a => ?_, fun q => ?_⟩
  · rw [j4 v fun h => hv (V.sub (Or.inr (Or.inl h))), hc v fun h => hv (V.sub (Or.inl h))]
    exact Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hu1 v) hv
  · rw [j4 _ (by rw [hw]; exact s.v0_St)]
    by_cases h : ((l : ℕ) : 𝓞 (Lp L)) ∈ s.v0.asIdeal
    · rw [h2 ⟨s.v0, h⟩]
      exact one_mem _
    · rw [hc _ (by rwa [hw])]
      exact (Subgroup.mem_inf.1 u.2).2
  · rw [j4 _ (by rw [hw]; exact fun h => s.St_l _ h v.2), h2]
  · rw [map_mul, map_inv, j2, hc _ (by rw [hw]; exact s.St_l _ a.2)]
    exact inv_mul_cancel _
  · rw [j4 _ fun h => Q.notS q (Or.inr (Or.inl h)), hc _ fun h => Q.notS q (Or.inl h)]
    exact Subgroup.mem_iInf.1 hu2 q
private theorem ne_inf (ι : Qbar l ≃+* ℂ) (lam : Wt L l n) {x : UA L n} (hx : x ∈ GlobalTheory.UnitaryBC.finU L n) :
    infRep (V := V) ι lam x = 1 := by
  have h : ∀ τ, cEmb τ x = 1 := fun τ => by
    unfold cEmb
    rw [MonoidHom.comp_apply, MonoidHom.mem_ker.1 hx, map_one]
  unfold infRep
  rw [MonoidHom.comp_apply, ← map_one PiTensorProduct.mapMonoidHom]
  congr 1
  funext e
  change GlobalTheory.Branching.sqRep ℂ n _ (cEmb _ x) = 1
  rw [h, map_one]
private theorem ne_lin (ι : Qbar l ≃+* ℂ) {lam : Wt L l n} {d : ℕ}
    (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) (ℓ) :
    ∃ T : (Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) → Fin d → ℂ) →ₗ[ℂ] (UA L n → ℂ), ∀ F, T F = toForm ι e F ℓ :=
  ⟨{ toFun := fun F => toForm ι e F ℓ
     map_add' := fun F F' => funext fun g => by simp [toForm]
     map_smul' := fun c F => funext fun g => by simp [toForm] }, fun _ => rfl⟩
end
theorem UpperTheory.V.Hi.nonempty_unitary_hecke_parts :
    _root_.UpperTheory.V.Af.HypothesesH' → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ), ∀ (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O), _root_.UpperTheory.V.Hi.CaseU.TypeForAlt r ι τ₀ →
    ∀ (lam : Wt L l n) (d : ℕ) (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ), IsBasis ι e ξ →
    ∀ σ : Submodule ℂ (UA L n → ℂ), IsAutRepU σ → (∀ x : Emb l (fun v : V.frame.Vl => s.w v.1), HasWeightAt σ (ι.toRingHom.comp x.res) (lam x.res).dual) → (∀ w : Plc L, w.under (𝓞 (Lp L)) ∉ V.S' → IsUnramU σ w) → (∃ τ : SmIrr (GLw n (s.w s.v0)), IsCompAlong σ (locU n (s.w s.v0)) ((cLoc (s.w s.v0)).comp (locU n (s.w s.v0)).subtype) τ.ρ ∧ fixd τ.ρ (Kc _ n 1) ≠ ⊥) → (∀ t, r.IsTeich t → ∀ u : s.St, ∃ τ : SmIrr (GLw n (s.w u)), IsCompAlong σ (locU n (s.w u)) ((cLoc (s.w u)).comp (locU n (s.w u)).subtype) τ.ρ ∧ ∀ rc, _root_.UpperTheory.Zero.LLC.IsRecT (s.hw u) rc → IsTypeWD (s.hw u) (fun i => W.pushCh (ι.toRingHom.comp (algebraMap c.O (Qbar l))) ((t i).comp (V.pr.comp (Ine (F := L) (s.A u)).subtype))) (rc (algNorm τ))) → YOf Q ι τ₀ e ξ σ ≠ ⊥ := by
  intro _ l _ L Ω _ _ _ _ _ _ s n hn V Q c r ι m τ₀ hτ lam d e ξ he σ hσ hwt hun h0 hty
  obtain ⟨hw, hsp⟩ := UpperTheory.under_chosen_place_and_isSplitAt_of_decomp_le l L Ω s
  obtain ⟨t, ht⟩ := ne_isTeich c r
  choose τ hτc hτw using hty t ht
  choose j h1 h2 _ h3 using fun u : s.St => (secU l L Ω s n hn (wt s u) (hsp _ (by
    rw [hw]
    exact s.split _ (Or.inr (Or.inl u.2))))).1
  obtain ⟨φ, hφ, hφ0, hφK⟩ := UpperTheory.exists_nonzero_form_fixed_by_level_of_unramified l L Ω s n hn V Q σ hσ hun h0
  obtain ⟨J, j1, j2, j3, F₀, hF0, hF1, hF2⟩ := ne_type (fun u : s.St => s.hw u)
    (fun a b hab => Subtype.ext ((hw _).symm.trans (hab.trans (hw _)))) j h1 h2 h3 _ _ (hτ t ht) hσ τ hτc hτw (neK n Q)
    (fun k hk => (mem_neK.1 hk).2.2.2.2.1) ((Submodule.ne_bot_iff _).2 ⟨φ, ⟨hφ, fun k hk => by
      obtain ⟨a1, a2, a3, a4, a5, a6⟩ := mem_neK.1 hk
      exact hφK k a1 a2 a3 a4 a5 a6⟩, hφ0⟩)
  set τ₁ := (Matrix.GeneralLinearGroup.map (ι.toRingHom.comp (algebraMap c.O (Qbar l)))).comp τ₀ with hτ₁
  let N : Submodule ℂ (Fin m → UA L n → ℂ) :=
    { carrier := {F | (∀ i, F i ∈ σ ⊓ fixd (RU L n) (neK n Q)) ∧
        ∀ (k : KT n (wt s)) i, ∑ a, τ₁ k i a • RU L n (J k) (F a) = F i}
      add_mem' := fun {a b} ha hb => ⟨fun i => add_mem (ha.1 i) (hb.1 i), fun k i => by
        simp only [Pi.add_apply, map_add, smul_add, Finset.sum_add_distrib, ha.2, hb.2]⟩
      zero_mem' := ⟨fun i => zero_mem _, fun k i => by simp⟩
      smul_mem' := fun z a ha => ⟨fun i => Submodule.smul_mem _ z (ha.1 i), fun k i => by
        simp only [Pi.smul_apply, map_smul, smul_comm _ z, ← Finset.smul_sum, ha.2]⟩ }
  obtain ⟨hfin, hbij⟩ := UpperTheory.placeEmbeddings_bijective_infinitePlaces l L Ω s V ι
  have hcomm : ∀ x ∈ infU L n, ∀ k ∈ GlobalTheory.UnitaryBC.finU L n, ∀ ψ, RU L n k (RU L n x ψ) = RU L n x (RU L n k ψ) :=
    fun x hx k hk ψ => by rw [GlobalTheory.DefU.RU_RU, GlobalTheory.DefU.RU_RU, GlobalTheory.DefU.fin_mul_inf hk hx]
  obtain ⟨Φ, hΦ0, hΦN, hΦ⟩ := UpperTheory.exists_tensor_dual_embedding_of_hasWeightAt L n hn _ _ hbij (fun x => lam x.res) σ hσ hwt m N
    ((Submodule.ne_bot_iff _).2 ⟨F₀, ⟨hF1, hF2⟩, hF0⟩) (fun F hF k => (hF.1 k).1) fun x hx F hF =>
      ⟨fun i => ⟨hσ.stable _ _ (hF.1 i).1, fun k hk => by rw [hcomm x hx k (mem_neK.1 hk).1, (hF.1 i).2 k hk]⟩, fun k i => by
        beta_reduce
        rw [← hF.2 k i, map_sum]
        exact Finset.sum_congr rfl fun a _ => by rw [map_smul, hcomm x hx _ (j1 _)]⟩
  obtain ⟨f1, -, f3, f4, f5⟩ := formU l L Ω s n hn V Q c m τ₀ ι lam d e ξ he _ fun _ => rfl
  have f6 : ∀ i : Fin m, ∃ F : Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) → Fin d → ℂ, F ∈ (hset Q τ₀).X.AF ξ ∧
      ∀ ℓ, toForm ι e F ℓ = Φ ℓ i := fun i => by
    have := f5 ((LinearMap.proj i : (Fin m → UA L n → ℂ) →ₗ[ℂ] (UA L n → ℂ)) ∘ₗ Φ) (fun ℓ => hσ.aut _ ((hΦN ℓ).1 i).1)
      fun ℓ x hx => hΦ ℓ x hx i
    exact this
  choose F hFA hF using f6
  have key0 : ∀ u : Ub n s, u ∈ UQ n Q → ∀ i,
      ∑ a, τ₁ (toKT n s u) i a • (fun g => F a (g * ((u : Ga l L n), 1))) - F i = 0 := fun u hu i => by
    obtain ⟨x, hx⟩ := f4 ((u : Ga l L n), 1)
    have hx1 : (away l L n).rangeRestrict (x : UA L n) = (u : Ga l L n) := congrArg Prod.fst hx
    have hx2 : ∀ v : V.frame.Vl, cLoc (s.w v.1) (x : UA L n) = 1 := congrFun (congrArg Prod.snd hx)
    have hk := ne_dec J j1 j2 j3 u hu x x.2 hx1 hx2
    let A : Submodule ℂ (Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) → Fin d → ℂ) := (hset Q τ₀).X.AF ξ
    have hF' : ∀ a, (fun g => F a (g * ((u : Ga l L n), 1))) ∈ A := fun a γ g =>
      (congrArg (F a) (mul_assoc _ _ _)).trans (hFA a γ _)
    refine f1 _ (A.sub_mem (A.sum_mem fun a _ => A.smul_mem _ (hF' a)) (hFA i)) fun ℓ => ?_
    obtain ⟨T, hT⟩ := ne_lin ι e ℓ
    have e2 : ∀ a, T (fun g => F a (g * ((u : Ga l L n), 1))) = RU L n (J (toKT n s u)) (Φ ℓ a) := fun a => by
      have e3 := f3 (F a) ℓ x
      rw [ne_inf ι lam (inv_mem x.2), hF] at e3
      simp only [hx] at e3
      rw [hT, ← ((hΦN ℓ).1 a).2 _ hk, GlobalTheory.DefU.RU_RU, mul_inv_cancel_left]
      exact e3.symm
    refine (hT _).symm.trans ?_
    rw [map_sub, map_sum, hT, hF, sub_eq_zero]
    simp only [map_smul, e2]
    exact (hΦN ℓ).2 _ i
  have key : ∀ u : Ub n s, u ∈ UQ n Q → ∀ i g k,
      ∑ a, τ₁ (toKT n s u) i a * F a (g * ((u : Ga l L n), 1)) k = F i g k := fun u hu i g k => by
    have := congrFun (congrFun (sub_eq_zero.1 (key0 u hu i)) g) k
    rw [Finset.sum_apply, Finset.sum_apply] at this
    exact this
  refine (Submodule.ne_bot_iff _).2 ⟨F, ⟨⟨fun i _ => hFA i, fun u hu => funext fun i => funext fun g => funext fun k => ?_⟩,
    Submodule.subset_span fun i ℓ => ?_⟩, fun h => hΦ0 (LinearMap.ext fun ℓ => funext fun i => ?_)⟩
  · exact key u hu i g k
  · rw [hF]
    exact ((hΦN ℓ).1 i).1
  · obtain ⟨T, hT⟩ := ne_lin ι e ℓ
    have h' : F i = 0 := congrFun h i
    rw [← hF, ← hT, h', map_zero]
    rfl
end
