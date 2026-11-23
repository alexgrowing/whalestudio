import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.DualPair
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.OmFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.PlSub

open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

section Abs

variable {K R M : Type} [Group K] [CommRing R] [Ring M] [Module R M] (ρ z : K → M) (χ : K → R)
  (h1 : ρ 1 = 1) (hm : ∀ g h, ρ (g * h) = ρ g * ρ h) (c1 : χ 1 = 1) (cm : ∀ g h, χ (g * h) = χ g * χ h)
  (hz : ∀ g h, z (g * h) = z g + χ g • (ρ g * z h * ρ g⁻¹))

include h1 c1 hz in
private theorem twisted_cocycle_apply_one : z 1 = 0 := by
  have := hz 1 1
  rw [mul_one, inv_one, h1, c1, one_mul, mul_one, one_smul] at this
  exact left_eq_add.1 this

private theorem tw_inv {N : Type} [Monoid N] (ρ : K → N) (h1 : ρ 1 = 1) (hm : ∀ g h, ρ (g * h) = ρ g * ρ h)
    {g : K} (hg : ρ g = 1) : ρ g⁻¹ = 1 := by
  have := hm g g⁻¹
  rw [mul_inv_cancel, h1, hg, one_mul] at this
  exact this.symm

include h1 hm hz in
private theorem tw_add {g : K} (hg : ρ g = 1) (hc : χ g = 1) (h : K) : z (g * h) = z g + z h := by
  rw [hz, tw_inv ρ h1 hm hg, hg, hc, one_mul, mul_one, one_smul]

include h1 hm c1 hz in
private theorem tw_pow {g : K} (hg : ρ g = 1) (hc : χ g = 1) (k : ℕ) : ρ (g ^ k) = 1 ∧ z (g ^ k) = k • z g := by
  induction k with
  | zero => rw [pow_zero, zero_smul]; exact ⟨h1, twisted_cocycle_apply_one ρ z χ h1 c1 hz⟩
  | succ k ih =>
    rw [pow_succ', hm, tw_add ρ z χ h1 hm hz hg hc, hg, ih.1, ih.2, one_mul, succ_nsmul']
    exact ⟨rfl, rfl⟩

include h1 hm c1 cm hz in
private theorem tw_U [TopologicalSpace K] (cρ : IsLocallyConstant ρ) (cχ : IsLocallyConstant χ)
    (cz : IsLocallyConstant z) :
    ∃ U : OpenNormalSubgroup K, ∀ g, g ∈ U ↔ ρ g = 1 ∧ χ g = 1 ∧ z g = 0 := by
  let S : Subgroup K :=
    { carrier := {g | ρ g = 1 ∧ χ g = 1 ∧ z g = 0}
      one_mem' := ⟨h1, c1, twisted_cocycle_apply_one ρ z χ h1 c1 hz⟩
      mul_mem' := fun {a b} ha hb => ⟨by rw [hm, ha.1, hb.1, one_mul], by rw [cm, ha.2.1, hb.2.1, one_mul],
        by rw [tw_add ρ z χ h1 hm hz ha.1 ha.2.1, ha.2.2, hb.2.2, add_zero]⟩
      inv_mem' := fun {a} ha => ⟨tw_inv ρ h1 hm ha.1, tw_inv χ c1 cm ha.2.1, by
        have := tw_add ρ z χ h1 hm hz ha.1 ha.2.1 a⁻¹
        rw [mul_inv_cancel, twisted_cocycle_apply_one ρ z χ h1 c1 hz, ha.2.2, zero_add] at this
        exact this.symm⟩ }
  have hN : S.Normal := ⟨fun u hu g => ⟨by
      rw [hm, hm, hu.1, mul_one, ← hm, mul_inv_cancel, h1], by
      rw [cm, cm, hu.2.1, mul_one, ← cm, mul_inv_cancel, c1], by
      rw [mul_assoc, hz, tw_add ρ z χ h1 hm hz hu.1 hu.2.1, hu.2.2, zero_add, ← hz, mul_inv_cancel,
        twisted_cocycle_apply_one ρ z χ h1 c1 hz]⟩⟩
  have hO : IsOpen (S : Set K) := (cρ {1}).inter ((cχ {1}).inter (cz {0}))
  exact ⟨⟨⟨S, hO⟩, hN⟩, fun g => Iff.rfl⟩

end Abs

private theorem tw_lc {Γ R : Type} [TopologicalSpace Γ] {n : ℕ} (f : Γ → Matrix (Fin n) (Fin n) R)
    (h : ∀ i j, IsLocallyConstant fun g => f g i j) : IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g0
  have : ∀ᶠ g in nhds g0, ∀ i j, f g i j = f g0 i j :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => (h i j).eventually_eq g0
  filter_upwards [this] with g hg
  exact Matrix.ext hg

private theorem pow_mem_of_PL (l : ℕ) {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    (H : Subgroup Γ) (V : Set Γ) (hV : IsOpen V) (hle : (PL l H : Set Γ) ⊆ V) : ∀ h ∈ H, ∃ e : ℕ, h ^ l ^ e ∈ V := by
  let ι := {U : OpenNormalSubgroup Γ // ∀ h ∈ H, ∃ e : ℕ, h ^ l ^ e ∈ U}
  haveI : Nonempty ι := ⟨⟨⟨⊤, Subgroup.normal_top⟩, fun h _ => ⟨0, trivial⟩⟩⟩
  have hd : Directed (· ⊇ ·) fun U : ι => (U.1 : Set Γ) := by
    intro U U'
    refine ⟨⟨U.1 ⊓ U'.1, fun h hh => ?_⟩, fun a ha => ha.1, fun a ha => ha.2⟩
    obtain ⟨e, he⟩ := U.2 h hh
    obtain ⟨e', he'⟩ := U'.2 h hh
    refine ⟨e + e', ?_, ?_⟩
    · rw [pow_add, pow_mul]
      exact U.1.toSubgroup.pow_mem he _
    · rw [pow_add, mul_comm, pow_mul]
      exact U'.1.toSubgroup.pow_mem he' _
  have hs : Vᶜ ∩ ⋂ U : ι, (U.1 : Set Γ) = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun a ha => ha.1 (hle ?_)
    have := Set.mem_iInter.1 ha.2
    simp only [PL, SetLike.mem_coe, Subgroup.mem_iInf]
    exact fun U hU => this ⟨U, hU⟩
  obtain ⟨U, hU⟩ := hV.isClosed_compl.isCompact.elim_directed_family_closed (fun U : ι => (U.1 : Set Γ))
    (fun U => U.1.toOpenSubgroup.isClosed) hs hd
  intro h hh
  obtain ⟨e, he⟩ := U.2 h hh
  refine ⟨e, ?_⟩
  by_contra hn
  exact Set.eq_empty_iff_forall_notMem.1 hU _ ⟨hn, he⟩

private theorem lc_padic {l : ℕ} [Fact l.Prime] {R : Type} [CommRing R] (f : ℤ_[l] →+* R) (m : ℕ)
    (hl : (l : R) ^ m = 0) : IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro y0
  have hp : (0 : ℝ) < (l : ℝ) ^ (-m : ℤ) := zpow_pos (by exact_mod_cast (Fact.out : l.Prime).pos) _
  filter_upwards [Metric.closedBall_mem_nhds y0 hp] with y hy
  rw [Metric.mem_closedBall, dist_eq_norm, PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton] at hy
  obtain ⟨c, hc⟩ := hy
  rw [← sub_eq_zero, ← map_sub, hc, map_mul, map_pow, map_natCast, hl, zero_mul]

private theorem pow_one_padic {l : ℕ} [Fact l.Prime] {R : Type} [CommRing R] (f : ℤ_[l] →+* R) (m : ℕ)
    (hl : (l : R) ^ m = 0) (a : ℤ_[l]) (ha : PadicInt.toZMod a = 1) : f (a ^ l ^ m) = 1 := by
  have : a - 1 ∈ RingHom.ker (PadicInt.toZMod (p := l)) := by
    rw [RingHom.mem_ker, map_sub, ha, map_one, sub_self]
  rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at this
  obtain ⟨c, hc⟩ := dvd_sub_pow_of_dvd_sub this m
  rw [one_pow] at hc
  rw [eq_add_of_sub_eq hc, map_add, map_mul, map_pow, map_natCast, pow_succ, hl]
  simp

private theorem rho_pow (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (O : Type) [CommRing O]
    [IsLocalRing O] [Algebra ℤ_[l] O] (n : ℕ) (y : Pt G0.frame O n) (m : ℕ)
    (hPL : ∀ g : G0.G₀, (g : G0.Γ) ∈ PL l T.H.toSubgroup → y.ρ g = 1)
    (hc : IsLocallyConstant fun g : G0.G₀ => red m (mat y.ρ g)) (g : G0.G₀)
    (hg : (g : G0.Γ) ∈ T.H) : ∃ e : ℕ, red m (mat y.ρ (g ^ l ^ e)) = 1 := by
  obtain ⟨e, g', h1, h2⟩ := pow_mem_of_PL l T.H.toSubgroup _
    (G0.η_open.isOpenMap_subtype_val _ (hc.isOpen_fiber 1)) (fun a ha => by
    have hη : a ∈ G0.η.ker := by
      have ha' := ha
      simp only [PL, SetLike.mem_coe, Subgroup.mem_iInf] at ha'
      exact ha' ⟨⟨G0.η.ker, G0.η_open⟩, MonoidHom.normal_ker _⟩ fun h hh =>
        ⟨0, by rw [pow_zero, pow_one]; exact T.H_η h hh⟩
    refine ⟨⟨a, hη⟩, ?_, rfl⟩
    show red m (mat y.ρ _) = 1
    simp [red, mat, hPL ⟨a, hη⟩ ha]) g hg
  have h3 : g' = g ^ l ^ e := Subtype.ext h2
  subst h3
  exact ⟨e, h1⟩

theorem UpperTheory.V.Th.plKill :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (y : Pt G0.frame O n) (m : ℕ) (G : Glob l L) (h : G.Hom G0), (∀ g : G0.G₀, (g : G0.Γ) ∈ PL l T.H.toSubgroup → y.ρ g = 1) → ∀ z : G.G₀ → Mm O n m, IsLocallyConstant z → (∀ g g', z (g * g') = z g + epsm O G m g • (y.ρm h m g * z g' * y.ρm h m g⁻¹)) → ∀ g : G.G₀, (g : G.Γ) ∈ PL l (T.H.toSubgroup.comap h.p) → z g = 0 ∧ y.ρm h m g = 1 ∧ epsm O G m g = 1 := by
  intro l _ L G0 T O _ _ _ _ _ n y m G h hPL z cz hz g hg
  obtain ⟨-, -, hk, -⟩ := (omFacts l O).2 m
  have hl : (l : Om O m) ^ m = 0 := by
    have := hk 1
    rwa [nsmul_eq_mul, mul_one, Nat.cast_pow] at this
  have hp : Continuous fun g : G.G₀ => h.p₀ g :=
    Continuous.subtype_mk (h.cont.comp continuous_subtype_val) _
  have h0 : IsLocallyConstant fun g : G0.G₀ => red m (mat y.ρ g) := tw_lc _ fun i j => y.cont i j m
  have c1 : IsLocallyConstant fun g : G.G₀ => y.ρm h m g := h0.comp_continuous hp
  let f : ℤ_[l] →+* Om O m := (algebraMap O (Om O m)).comp (algebraMap ℤ_[l] O)
  have c2 : IsLocallyConstant fun g : G.G₀ => epsm O G m g :=
    (lc_padic f m hl).comp_continuous (Units.continuous_val.comp (G.ε_cont.comp continuous_subtype_val))
  have r1 : y.ρm h m 1 = 1 := by simp [Pt.ρm, red, mat]
  have r2 : ∀ a b, y.ρm h m (a * b) = y.ρm h m a * y.ρm h m b := fun a b => by
    simp [Pt.ρm, red, mat, Matrix.map_mul]
  have e1 : epsm O G m ((1 : G.G₀) : G.Γ) = 1 := by simp [epsm]
  have em : ∀ a b : G.G₀, epsm O G m ((a * b : G.G₀) : G.Γ) = epsm O G m a * epsm O G m b := by
    intro a b
    simp [epsm]
  obtain ⟨U, hU⟩ := tw_U (K := G.G₀) (fun g => y.ρm h m g) z (fun g => epsm O G m g) r1 r2 e1 em hz c1 c2 cz
  haveI := T.H.isNormal'
  have hsub := pl_sub l G.Γ (T.H.toSubgroup.comap h.p) G.η.ker G.η_open
    (fun a ha => by rw [MonoidHom.mem_ker, ← h.η]; exact T.H_η _ ha) U fun a ha => by
    obtain ⟨e, he⟩ := rho_pow l L G0 T O n y m hPL h0 (h.p₀ a) ha
    have he' : y.ρm h m (a ^ l ^ e) = 1 := by rw [Pt.ρm, map_pow]; exact he
    have hε : ∀ b : G.G₀, h.p b ∈ T.H → epsm O G m ((b ^ l ^ m : G.G₀) : G.Γ) = 1 := fun b hb => by
      have := pow_one_padic f m hl _ (T.H_ε _ hb)
      rw [h.ε] at this
      rw [← this]
      simp [epsm, f]
    have hρp : ∀ (b : G.G₀) (k : ℕ), y.ρm h m b = 1 → y.ρm h m (b ^ k) = 1 := fun b k hb => by
      induction k with
      | zero => rw [pow_zero]; exact r1
      | succ k ih => rw [pow_succ, r2, ih, hb, one_mul]
    have hH : ∀ k : ℕ, h.p ((a ^ k : G.G₀) : G.Γ) ∈ T.H := fun k => (T.H.toSubgroup.comap h.p).pow_mem ha k
    have := tw_pow (K := G.G₀) (fun g => y.ρm h m g) z (fun g => epsm O G m g) r1 r2 e1 hz
      (hρp _ (l ^ m) he') (hε _ (hH _)) (l ^ m)
    refine ⟨e + m + m, (hU _).2 ⟨?_, ?_, ?_⟩⟩
    · rw [pow_add, pow_add, pow_mul, pow_mul]
      exact this.1
    · rw [pow_add, pow_mul]
      exact hε _ (hH _)
    · rw [pow_add, pow_add, pow_mul, pow_mul]
      exact this.2.trans (Matrix.ext fun i j => hk _)
  obtain ⟨u1, u2, u3⟩ := (hU g).1 (hsub g hg)
  exact ⟨u3, u1, u2⟩
