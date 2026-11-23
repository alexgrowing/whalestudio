import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.OverOf4
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.QuadraticSplitting.QuadSplit

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Cu

private theorem closed_fix {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (F E : IntermediateField ℚ Ω) :
    IsClosed ((E.fixingSubgroup.comap (resQ F) : Subgroup (G F Ω)) : Set (G F Ω)) := by
  haveI : Algebra.IsAlgebraic F Ω := Algebra.IsAlgebraic.tower_top (K := ℚ) F
  have e : ((E.fixingSubgroup.comap (resQ F) : Subgroup (G F Ω)) : Set (G F Ω)) =
      ⋂ x ∈ E, (MulAction.stabilizer (Ω ≃ₐ[F] Ω) x : Set (Ω ≃ₐ[F] Ω)) := by
    ext g
    simp only [SetLike.mem_coe, Subgroup.mem_comap, Set.mem_iInter, MulAction.mem_stabilizer_iff]
    rw [IntermediateField.mem_fixingSubgroup_iff]
    rfl
  rw [e]
  exact isClosed_biInter fun x _ => Subgroup.isClosed_of_isOpen _ (stabilizer_isOpen_of_isIntegral x)

private theorem lim_pt {Γ : Type} [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ] (l : ℕ) [Fact l.Prime]
    (ε : Γ →* ℤ_[l]ˣ) (hε : Continuous ε) (S : Set Γ) (hS : IsClosed S) (g : Γ)
    (hg : (l : ℤ_[l]) ∣ (ε g : ℤ_[l]) - 1) (hm : ∀ n : ℕ, g ^ l ^ n ∈ S) : ∃ h ∈ S, ε h = 1 := by
  have ht : Filter.Tendsto (fun n : ℕ => ((ε (g ^ l ^ n) : ℤ_[l]ˣ) : ℤ_[l])) Filter.atTop (nhds 1) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
    have h0 : Filter.Tendsto (fun n : ℕ => ((l : ℝ)⁻¹) ^ n) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hl)
    refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) h0
    have h2 := dvd_sub_pow_of_dvd_sub hg n
    rw [one_pow] at h2
    have h3 := (pow_dvd_pow _ n.le_succ).trans h2
    rw [map_pow, Units.val_pow_eq_pow_val, inv_pow, ← zpow_natCast, ← zpow_neg,
      PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton]
    exact h3
  obtain ⟨h, hh, hc⟩ := hS.isCompact.exists_mapClusterPt (f := Filter.atTop) (u := fun n : ℕ => g ^ l ^ n)
    (Filter.tendsto_principal.2 (Filter.Eventually.of_forall hm))
  refine ⟨h, hh, Units.ext ?_⟩
  have hc' := hc.continuousAt_comp (Units.continuous_val.comp hε).continuousAt
  exact eq_of_nhds_neBot (hc'.clusterPt.mono ht)

private theorem dvd_of_om {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    (D : Raw Ω c) (hD : D.Good) (g : G ℚ Ω) (hg : D.om g = 1) : (l : ℤ_[l]) ∣ (cycZ ℚ Ω l g : ℤ_[l]) - 1 := by
  obtain ⟨-, -, hloc, -⟩ := dvrFacts l c.O
  have h := hD.om_bar g
  simp only [Raw.bar, hg, Units.val_one] at h
  have h1 : residue c.O (algebraMap ℤ_[l] c.O ((cycZ ℚ Ω l g : ℤ_[l]) - 1)) = 0 := by
    rw [map_sub, map_sub, map_one, h, sub_eq_zero]
    rfl
  rw [residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff] at h1
  have h2 : (cycZ ℚ Ω l g : ℤ_[l]) - 1 ∈ maximalIdeal ℤ_[l] := fun hu => h1 (hu.map _)
  rwa [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at h2

section
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [hl : Fact l.Prime] {c : Coef l} {D : Raw Ω c}
  (T : Tower D)

private theorem rb_al (g : G T.F Ω) :
    T.rb wAl g = residue c.O ((chi D T.pr 0 (resQ T.F g) * (chi D T.pr 1 (resQ T.F g))⁻¹ : c.Oˣ) : c.O) := by
  show residue c.O (((chi D T.pr 0 (resQ T.F g) * (chi D T.pr 1 (resQ T.F g))⁻¹) ^ (1 : ℤ) *
    (chi D T.pr 0 (resQ T.F g) * (chi D T.pr 2 (resQ T.F g))⁻¹) ^ (0 : ℤ) : c.Oˣ) : c.O) = _
  rw [zpow_one, zpow_zero, mul_one]

private theorem rb_le {T₀ : Tower D} (h : T₀.Le T) (g : G T.F Ω) : T.rb wAl g = T₀.rb wAl (resLe h.le g) := by
  rw [rb_al, rb_al, h.pr]
  try rfl

private noncomputable def eta : G T.F Ω →* (ResidueField c.O)ˣ :=
  (Units.map (residue c.O).toMonoidHom).comp ((T.fr ∅).rt wAl)

private theorem eta_val (g : G T.F Ω) : (eta T g : ResidueField c.O) = T.rb wAl g := rfl

private theorem eta_iff {K' : IntermediateField ℚ Ω}
    (hon : ∀ g : G T.F Ω, resQ T.F g ∈ K'.fixingSubgroup → T.rb wAl g = 1)
    (hoff : ∀ g : G T.F Ω, resQ T.F g ∉ K'.fixingSubgroup → T.rb wAl g = -1) (hn : (-1 : ResidueField c.O) ≠ 1)
    (g : G T.F Ω) : eta T g = 1 ↔ resQ T.F g ∈ K'.fixingSubgroup := by
  rw [← Units.val_eq_one, eta_val]
  by_cases h : resQ T.F g ∈ K'.fixingSubgroup
  · exact ⟨fun _ => h, fun _ => hon g h⟩
  · rw [hoff g h]
    exact ⟨fun e => absurd e hn, fun e => absurd e h⟩

private theorem eta_sq {K' : IntermediateField ℚ Ω}
    (hon : ∀ g : G T.F Ω, resQ T.F g ∈ K'.fixingSubgroup → T.rb wAl g = 1)
    (hoff : ∀ g : G T.F Ω, resQ T.F g ∉ K'.fixingSubgroup → T.rb wAl g = -1) (g : G T.F Ω) : eta T g ^ 2 = 1 := by
  refine Units.ext ?_
  rw [Units.val_pow_eq_pow_val, eta_val, Units.val_one]
  by_cases h : resQ T.F g ∈ K'.fixingSubgroup
  · rw [hon g h, one_pow]
  · rw [hoff g h, neg_one_sq]

private theorem eta_om (hD : D.Good) (K' : IntermediateField ℚ Ω)
    (hk' : ∀ g, eta T g = 1 ↔ resQ T.F g ∈ K'.fixingSubgroup) (hsq : ∀ g, eta T g ^ 2 = 1)
    (hne : ∀ g ∈ T.G', resQ T.F g ∈ K'.fixingSubgroup) (g : G T.F Ω) (hg' : g ∈ T.GalL)
    (hg : D.om (resQ T.F g) = 1) : eta T g = 1 := by
  haveI : Algebra.IsAlgebraic T.F Ω := Algebra.IsAlgebraic.tower_top (K := ℚ) T.F
  haveI : IsAlgClosure T.F Ω := ⟨IsAlgClosure.isAlgClosed ℚ, inferInstance⟩
  haveI : IsGalois T.F Ω := {}
  haveI : CompactSpace (G T.F Ω) := inferInstanceAs (CompactSpace (Ω ≃ₐ[T.F] Ω))
  have hk'' : ∀ g, eta T g = 1 ↔ g ∈ K'.fixingSubgroup.comap (resQ T.F) := fun g => by
    rw [Subgroup.mem_comap, hk']
  have hc : Continuous fun h : G T.F Ω => g⁻¹ * h := continuous_mul_left _
  have h0 : IsClosed (T.GalL : Set (G T.F Ω)) := closed_fix T.F T.K
  have hd : (l : ℤ_[l]) ∣ (cycZ T.F Ω l g : ℤ_[l]) - 1 := dvd_of_om D hD (resQ T.F g) hg
  obtain ⟨h, ⟨h1, h2⟩, h3⟩ := lim_pt l (cycZ T.F Ω l) (continuous_cycZ T.F Ω l) _
    (h0.inter ((closed_fix T.F K').preimage hc)) g hd (fun n => ⟨T.GalL.pow_mem hg' _, by
      refine (hk'' _).1 ?_
      obtain ⟨m, hm⟩ := (hl.out.odd_of_ne_two hD.l_odd).pow (n := n)
      rw [map_mul, map_inv, map_pow, hm, pow_succ, pow_mul, hsq g, one_pow, one_mul, inv_mul_cancel]⟩)
  have h4 : eta T h = 1 := (hk' h).2 (hne h ⟨h1, h3⟩)
  have h5 := (hk'' _).2 h2
  rwa [map_mul, h4, mul_one, map_inv, inv_eq_one] at h5

private theorem eta_mul (g : G T.F Ω) :
    eta T g * Raw.bar (chi D T.pr 1) (resQ T.F g) = Raw.bar (chi D T.pr 0) (resQ T.F g) ∧
    eta T g * Raw.bar (chi D T.pr 3) (resQ T.F g) = Raw.bar (chi D T.pr 2) (resQ T.F g) := by
  have e : (T.fr ∅).rt wAl g = chi D T.pr 0 (resQ T.F g) * (chi D T.pr 1 (resQ T.F g))⁻¹ := by
    show (chi D T.pr 0 (resQ T.F g) * (chi D T.pr 1 (resQ T.F g))⁻¹) ^ (1 : ℤ) *
      (chi D T.pr 0 (resQ T.F g) * (chi D T.pr 2 (resQ T.F g))⁻¹) ^ (0 : ℤ) = _
    rw [zpow_zero, zpow_one, mul_one]
  have e' : (T.fr ∅).rt wAl g = chi D T.pr 2 (resQ T.F g) * (chi D T.pr 3 (resQ T.F g))⁻¹ := by
    rw [e]
    generalize resQ T.F g = s
    cases T.pr
    · show D.al s * D.Psi s * (D.Psi s)⁻¹ = D.al s * 1⁻¹
      rw [inv_one, mul_one, mul_inv_cancel_right]
    · show D.al s * 1⁻¹ = D.al s * D.Psi s * (D.Psi s)⁻¹
      rw [inv_one, mul_one, mul_inv_cancel_right]
  rw [eta_val]
  constructor
  · show residue c.O _ * residue c.O _ = residue c.O _
    rw [← map_mul, ← Units.val_mul, e, inv_mul_cancel_right]
  · show residue c.O _ * residue c.O _ = residue c.O _
    rw [← map_mul, ← Units.val_mul, e', inv_mul_cancel_right]

private theorem eta_mul' (hsq : ∀ g, eta T g ^ 2 = 1) (g : G T.F Ω) {u v : ResidueField c.O} (h : eta T g * u = v) :
    eta T g * v = u := by
  rw [← h, ← mul_assoc, ← Units.val_mul, ← pow_two, hsq g, Units.val_one, one_mul]

private noncomputable def etaL : T.GalL →* (ResidueField c.O)ˣ := (eta T).comp T.GalL.subtype

private theorem etaL_app (g : T.GalL) : etaL T g = eta T g := rfl

private theorem etaL_sq (hsq : ∀ g, eta T g ^ 2 = 1) : etaL T ^ 2 = 1 := by
  refine MonoidHom.ext fun g => ?_
  rw [MonoidHom.pow_apply, MonoidHom.one_apply, etaL_app, hsq]

private theorem etaL_perm (hsq : ∀ g, eta T g ^ 2 = 1) (i : Fin 4) : ∃ j, ∀ g : T.GalL,
    etaL T g * Raw.bar (chi D T.pr i) (resQ T.F g) = Raw.bar (chi D T.pr j) (resQ T.F g) := by
  simp only [etaL_app]
  match i with
  | 0 => exact ⟨1, fun g => eta_mul' T hsq g (eta_mul T g).1⟩
  | 1 => exact ⟨0, fun g => (eta_mul T g).1⟩
  | 2 => exact ⟨3, fun g => eta_mul' T hsq g (eta_mul T g).2⟩
  | 3 => exact ⟨2, fun g => (eta_mul T g).2⟩

end

theorem UpperTheory.V.Cu.alNe : AlNe := by
  intro Ω _ _ _ l hl d T hT hO
  by_contra hne
  have hne' : ∀ g ∈ T.G', resQ T.F g ∈ d.K'.fixingSubgroup := fun g hg => by_contra fun h => hne ⟨g, hg, h⟩
  have hon : ∀ g : G T.F Ω, resQ T.F g ∈ d.K'.fixingSubgroup → T.rb wAl g = 1 := fun g hg => by
    rw [rb_le T hT]
    exact d.quad.on (resLe hT.le g) hg
  have hoff : ∀ g : G T.F Ω, resQ T.F g ∉ d.K'.fixingSubgroup → T.rb wAl g = -1 := fun g hg => by
    rw [rb_le T hT]
    exact d.quad.off (resLe hT.le g) hg
  have hn : (-1 : ResidueField d.c.O) ≠ 1 := by
    obtain ⟨g, -, hg⟩ := hO.g3 wAl (by decide)
    by_cases h : resQ T.F g ∈ d.K'.fixingSubgroup
    · exact absurd (hon g h) hg
    · rw [hoff g h] at hg
      exact hg
  have hsq := eta_sq T hon hoff
  have key := hO.g3' (etaL T) (etaL_sq T hsq)
    (fun g hg => by rw [etaL_app]; exact eta_om T d.ctx.1 d.K' (eta_iff T hon hoff hn) hsq hne' g g.2 hg)
    (etaL_perm T hsq)
  obtain ⟨g, hg, hg'⟩ := hO.g3 wAl (by decide)
  have h1 := etaL_app T ⟨g, hg⟩
  rw [key, MonoidHom.one_apply] at h1
  apply hg'
  rw [← eta_val, ← h1, Units.val_one]
