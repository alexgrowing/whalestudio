import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HeckePairTop
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameParahoricRepSplitsAsProduct
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwJqInj
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwJqTheta
open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools GlobalTheory.PRep

section General

variable {G V : Type} [CommGroup G] [AddCommGroup V] [Module ℂ V]

private theorem pow_comm_rep (ρ : Representation ℂ G V) (t g : G) (c : ℂ) (m : ℕ) (v : V) :
    ((ρ t - algebraMap ℂ (Module.End ℂ V) c) ^ m) (ρ g v) =
      ρ g (((ρ t - algebraMap ℂ (Module.End ℂ V) c) ^ m) v) := by
  have h : Commute (ρ t - algebraMap ℂ (Module.End ℂ V) c) (ρ g) :=
    Commute.sub_left ((Commute.all t g).map ρ) (Algebra.commutes c (ρ g))
  exact LinearMap.congr_fun (h.pow_left m).eq v

private theorem pow_mem_sub (ρ : Representation ℂ G V) (N : Subrepresentation ρ) (t : G) (c : ℂ) (m : ℕ)
    (v : V) (hv : v ∈ N.toSubmodule) : ((ρ t - algebraMap ℂ (Module.End ℂ V) c) ^ m) v ∈ N.toSubmodule := by
  induction m with
  | zero => simpa using hv
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply, LinearMap.sub_apply, Module.algebraMap_end_apply]
    exact sub_mem (N.apply_mem_toSubmodule t ih) (N.toSubmodule.smul_mem c ih)

private theorem exists_nil {ρ : Representation ℂ G V} (hl : HasFiniteLength ρ) {c : G → ℂ} {x : V} (hx : x ≠ 0)
    (hxc : ∀ t, ∃ m : ℕ, ((ρ t - algebraMap ℂ (Module.End ℂ V) (c t)) ^ m) x = 0) :
    ∃ N : Subrepresentation ρ, N ≠ ⊤ ∧
      ∀ t, ∃ m : ℕ, ∀ v, ((ρ t - algebraMap ℂ (Module.End ℂ V) (c t)) ^ m) v ∈ N.toSubmodule := by
  haveI := ((hasFiniteLength_iff_wellFounded ρ).1 hl).1
  obtain ⟨N, hN, hmax⟩ := (wellFounded_gt (α := Subrepresentation ρ)).has_min {N | x ∉ N.toSubmodule}
    ⟨⊥, fun h => hx ((Submodule.mem_bot ℂ).1 h)⟩
  refine ⟨N, fun h => hN (by rw [h]; trivial), fun t => ?_⟩
  set f := ρ t - algebraMap ℂ (Module.End ℂ V) (c t) with hf
  let K : ℕ →o Subrepresentation ρ :=
    ⟨fun m => ⟨N.toSubmodule.comap (f ^ m), fun g v hv => by
        show (f ^ m) (ρ g v) ∈ N.toSubmodule
        rw [hf, pow_comm_rep]
        exact N.apply_mem_toSubmodule g hv⟩,
      monotone_nat_of_le_succ fun m v hv => by
        show (f ^ (m + 1)) v ∈ N.toSubmodule
        rw [add_comm, pow_add, Module.End.mul_apply]
        exact pow_mem_sub ρ N t _ 1 _ hv⟩
  obtain ⟨a, ha⟩ := WellFoundedGT.monotone_chain_condition K
  obtain ⟨b, hb⟩ := hxc t
  let R : Subrepresentation ρ := ⟨N.toSubmodule ⊔ LinearMap.range (f ^ (a + b)), fun g v hv => by
    obtain ⟨y, hy, _, ⟨z, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hv
    rw [map_add]
    exact Submodule.add_mem_sup (N.apply_mem_toSubmodule g hy) ⟨ρ g z, by rw [hf, pow_comm_rep]⟩⟩
  have hR : x ∉ R.toSubmodule := fun hv => by
    obtain ⟨y, hy, _, ⟨z, rfl⟩, h⟩ := Submodule.mem_sup.1 hv
    have h1 : z ∈ (K (b + (a + b))).toSubmodule := by
      show (f ^ (b + (a + b))) z ∈ N.toSubmodule
      rw [pow_add, Module.End.mul_apply, eq_sub_of_add_eq' h, map_sub, hb, zero_sub]
      exact neg_mem (pow_mem_sub ρ N t _ b _ hy)
    rw [← ha _ (by omega), ha (a + b) (by omega)] at h1
    exact hN (h ▸ add_mem hy h1)
  have hNR : N ≤ R := fun v hv => Submodule.mem_sup_left (S := N.toSubmodule) hv
  have hE : N = R := by
    by_contra hne
    exact hmax R hR (lt_of_le_of_ne hNR hne)
  refine ⟨a + b, fun v => ?_⟩
  rw [hE]
  exact Submodule.mem_sup_right ⟨v, rfl⟩

variable [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace.SeparableSpace G]

private theorem exists_form {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) (hl : HasFiniteLength ρ) {χ : G →* ℂˣ}
    {x : V} (hx : x ≠ 0)
    (hxc : ∀ t, ∃ m : ℕ, ((ρ t - algebraMap ℂ (Module.End ℂ V) (χ t : ℂ)) ^ m) x = 0) :
    IsSmoothChar χ ∧ ∃ l : V →ₗ[ℂ] ℂ, l ≠ 0 ∧ ∀ g v, l (ρ g v) = (χ g : ℂ) * l v := by
  obtain ⟨T, hT, hnil⟩ := exists_nil hl hx hxc
  haveI := ((hasFiniteLength_iff_wellFounded ρ).1 hl).1
  obtain ⟨M, hM, hTM⟩ := (eq_top_or_exists_le_coatom T).resolve_left hT
  have hi := isIrreducible_subQuot hM.covBy_top
  let p : (⊤ : Subrepresentation ρ).toRepresentation.IntertwiningMap (subQuot ⊤ M) :=
    ⟨Submodule.mkQ _, fun _ => rfl⟩
  have hs : IsSmooth (subQuot ⊤ M) :=
    IsSubquotient.isSmooth ⟨⊤, p, Submodule.Quotient.mk_surjective _⟩ hρ
  obtain ⟨μ, hμ⟩ := GlobalTheory.TorusEigenform.exists_char_of_isIrreducible hs hi
  have hμM : ∀ g v, ρ g v - (μ g : ℂ) • v ∈ M.toSubmodule := fun g v => by
    have := hμ g (Submodule.Quotient.mk ⟨v, trivial⟩)
    exact (Submodule.Quotient.eq (M.toSubmodule.comap (⊤ : Subrepresentation ρ).toSubmodule.subtype)
      (x := ⟨ρ g v, trivial⟩) (y := ⟨(μ g : ℂ) • v, trivial⟩)).1 this
  have hM' : M.toSubmodule < ⊤ := lt_top_iff_ne_top.2 fun h =>
    hM.1 (Subrepresentation.toSubmodule_injective h)
  obtain ⟨l, hl0, hlM⟩ := Submodule.exists_le_ker_of_lt_top _ hM'
  have hle : ∀ g v, l (ρ g v) = (μ g : ℂ) * l v := fun g v => by
    have := hlM (hμM g v)
    rwa [LinearMap.mem_ker, map_sub, map_smul, sub_eq_zero] at this
  obtain ⟨v, hv⟩ : ∃ v, l v ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hl0 (LinearMap.ext hn)
  have hμχ : μ = χ := MonoidHom.ext fun t => by
    obtain ⟨m, hm⟩ := hnil t
    have h1 : ∀ m : ℕ, l (((ρ t - algebraMap ℂ (Module.End ℂ V) (χ t : ℂ)) ^ m) v) =
        ((μ t : ℂ) - χ t) ^ m * l v := fun m => by
      induction m with
      | zero => simp
      | succ m ih =>
        rw [pow_succ', Module.End.mul_apply, LinearMap.sub_apply, Module.algebraMap_end_apply, map_sub, hle,
          map_smul, ih, smul_eq_mul]
        ring
    have h2 := hlM (hTM (hm v))
    rw [LinearMap.mem_ker, h1] at h2
    exact Units.ext (sub_eq_zero.1 (pow_eq_zero_iff'.1 ((mul_eq_zero.1 h2).resolve_right hv)).1)
  subst hμχ
  refine ⟨?_, l, hl0, hle⟩
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset ((hρ v).mem_nhds (by simp)) ?_)
  intro g hg
  have hg' : ρ g v = v := hg
  have h := hle g v
  rw [hg'] at h
  exact Units.ext (mul_right_cancel₀ hv (h.symm.trans (one_mul _).symm))

end General

theorem UpperTheory.V.AlgebraTools.jqEmbed :
    GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (C : Subgroup 𝓀[k]ˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → π.IsIrreducible → ∀ θ : (Fin n → kˣ) →* (Module.End ℂ (fixd π (iwC k n C)))ˣ, (∀ t, Dom t → (θ t : Module.End ℂ (fixd π (iwC k n C))) = hk π (iwC k n C) (diagT k (Fin n) t)) → ∀ χ : (Fin n → kˣ) →* ℂˣ, (⨅ t, Module.End.maxGenEigenspace (θ t : Module.End ℂ (fixd π (iwC k n C))) (χ t : ℂ)) ≠ ⊥ → ∃ ψ : Fin n → kˣ →* ℂˣ, (∀ i, IsSmoothChar (ψ i)) ∧ (∀ i, ∀ x ∈ unitsC k C, ψ i x = 1) ∧ torusChar ψ = χ * ((deltaHalf k fun _ : Fin n => Unit).comp (leviTorus k (Fin n)).toMonoidHom) ∧ IsSubquotient π (prinSeries ψ) := by
  intro hBZ k _ _ _ _ n C V _ _ π hπ hirr θ hθ χ hne
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hne
  set δ : (Fin n → kˣ) →* ℂˣ := (deltaHalf k fun _ : Fin n => Unit).comp (leviTorus k (Fin n)).toMonoidHom
    with hδ
  have hl : HasFiniteLength (jacB π) :=
    (hasFiniteLength_comp_iff _ _ (leviTorus k (Fin n)).surjective).2
      ((hBZ k).2.1 _ _ _ (points (Fin n)) _ π hπ (hasFiniteLength_of_isIrreducible hirr))
  let q : fixd π (iwC k n C) →ₗ[ℂ] Jacquet π (unipB k (Fin n)) :=
    (Submodule.mkQ _) ∘ₗ (fixd π (iwC k n C)).subtype
  have hq : ∀ t w, jacB π t (q w) = (δ t : ℂ) • q ((θ t : Module.End ℂ (fixd π (iwC k n C))) w) := fun t w => by
    have h : q ((θ t : Module.End ℂ (fixd π (iwC k n C))) w) = (((δ t)⁻¹ : ℂˣ) : ℂ) • jacB π t (q w) :=
      jqTheta k n C V π θ hθ t w
    rw [h, smul_smul, Units.mul_inv, one_smul]
  have hx : q v ≠ 0 := fun h => hv0 (jqInj k n C V π hπ v h)
  have hxc : ∀ t, ∃ m : ℕ, ((jacB π t - algebraMap ℂ (Module.End ℂ (Jacquet π (unipB k (Fin n)))) ((χ * δ) t : ℂ)) ^ m) (q v) = 0 := fun t => by
    obtain ⟨m, hm⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 ((Submodule.mem_iInf _).1 hv t)
    have h1 : ∀ m : ℕ, ((jacB π t - algebraMap ℂ (Module.End ℂ (Jacquet π (unipB k (Fin n)))) ((χ * δ) t : ℂ)) ^ m) (q v) =
        (δ t : ℂ) ^ m • q ((((θ t : Module.End ℂ (fixd π (iwC k n C))) - (χ t : ℂ) • 1) ^ m) v) := fun m => by
      induction m with
      | zero => simp
      | succ m ih =>
        rw [pow_succ', Module.End.mul_apply, ih, map_smul, pow_succ' (_ - _), Module.End.mul_apply,
          LinearMap.sub_apply, LinearMap.sub_apply, hq, Module.algebraMap_end_apply, map_sub,
          LinearMap.smul_apply, Module.End.one_apply, map_smul, MonoidHom.mul_apply, Units.val_mul,
          mul_comm (χ t : ℂ), mul_smul, ← smul_sub, smul_smul, pow_succ]
    exact ⟨m, by rw [h1, hm, map_zero, smul_zero]⟩
  haveI := GlobalTheory.TorusEigenform.secondCountableTopology_units k
  obtain ⟨hs, l, hl0, hle⟩ := exists_form (isSmooth_jacB hπ) hl hx hxc
  have htc : torusChar (fun i => (χ * δ).comp (MonoidHom.mulSingle (fun _ => kˣ) i)) = χ * δ :=
    MonoidHom.ext fun t => by
      rw [torusChar_apply]
      conv_rhs => rw [← Finset.univ_prod_mulSingle t, map_prod]
      rfl
  refine ⟨fun i => (χ * δ).comp (MonoidHom.mulSingle (fun _ => kˣ) i), fun i => hs.comp _ (continuous_mulSingle (A := fun _ => kˣ) i),
    fun i x hxC => ?_, htc, ?_⟩
  · have ht : Pi.mulSingle i x ∈ torC k n C := fun j _ => by
      by_cases h : j = i
      · subst h; simpa using hxC
      · simp [Pi.mulSingle_eq_of_ne h, one_mem]
    show (χ * δ) (Pi.mulSingle i x) = 1
    generalize (Pi.mulSingle i x : Fin n → kˣ) = t at ht ⊢
    have hO : t ∈ torusO k (Fin n) := fun j => by
      obtain ⟨u, -, hu⟩ := ht j trivial
      rw [← hu]
      exact (Valuation.integer.integers (valuation k)).one_of_isUnit (Units.isUnit u)
    have hfix : jacB π t (q v) = q v := by
      have h1 : δ t = 1 := UnramFixed.deltaHalf_torusO k hO
      have h2 : π (diagT k (Fin n) t) v = v := v.2 _ (Subgroup.mem_sup_right ⟨t, ht, rfl⟩)
      show jacB π t (Submodule.Quotient.mk (v : V)) = Submodule.Quotient.mk (v : V)
      rw [UnramFixed.jacB_apply, jacBU_mk, h2, ← hδ, h1]
      simp
    obtain ⟨m, hm⟩ := hxc t
    have h1 : ∀ m : ℕ, ((jacB π t - algebraMap ℂ (Module.End ℂ (Jacquet π (unipB k (Fin n)))) ((χ * δ) t : ℂ)) ^ m) (q v) =
        (1 - ((χ * δ) t : ℂ)) ^ m • q v := fun m => by
      induction m with
      | zero => simp
      | succ m ih =>
        rw [pow_succ', Module.End.mul_apply, ih, map_smul, LinearMap.sub_apply, hfix,
          Module.algebraMap_end_apply, pow_succ, mul_smul, sub_smul, one_smul]
    rw [h1] at hm
    exact Units.ext (sub_eq_zero.1 (pow_eq_zero_iff'.1 ((smul_eq_zero.1 hm).resolve_right hx)).1).symm
  · have key := GlobalTheory.SatakeExists.isSubquotient_of_eigenform hπ hirr (χ * δ) l hl0 hle
    rw [← htc] at key
    exact key
