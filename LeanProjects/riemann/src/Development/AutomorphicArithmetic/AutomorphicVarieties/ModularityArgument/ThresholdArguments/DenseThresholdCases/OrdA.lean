import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.OrdA
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
private theorem ordA_lin {W ι : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (f : ι → Module.End ℂ W) (hc : ∀ i j, Commute (f i) (f j)) (l : W →ₗ[ℂ] ℂ) (μ : ι → ℂ)
    (hl : ∀ i v, l (f i v) = μ i * l v) {w : W} (hw : l w ≠ 0) : ∃ v, v ≠ 0 ∧ ∀ i, f i v = μ i • v := by
  have htop := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute f
    (fun i j _ => hc i j) fun i => Module.End.iSup_maxGenEigenspace_eq_top (f i)
  obtain ⟨χ, u, hu, hlu⟩ : ∃ χ : ι → ℂ, ∃ u ∈ ⨅ i, (f i).maxGenEigenspace (χ i), l u ≠ 0 := by
    by_contra h
    push Not at h
    have : (⊤ : Submodule ℂ W) ≤ LinearMap.ker l := htop ▸ iSup_le fun χ u hu => h χ u hu
    exact hw (this trivial)
  have pw : ∀ i (x : ℂ) (m : ℕ) v, l (((f i - x • 1) ^ m) v) = (μ i - x) ^ m * l v := by
    intro i x m
    induction m with
    | zero => simp
    | succ m ih => intro v; rw [pow_succ, Module.End.mul_apply, ih]; simp [hl]; ring
  obtain rfl : μ = χ := funext fun i => by
    obtain ⟨m, hm⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 ((Submodule.mem_iInf _).1 hu i)
    have := pw i (χ i) m u
    rw [hm, map_zero, eq_comm, mul_eq_zero] at this
    exact sub_eq_zero.1 (eq_zero_of_pow_eq_zero (this.resolve_right hlu))
  let A : Set (Submodule ℂ W) :=
    {S | S ≠ ⊥ ∧ S ≤ (⨅ i, (f i).maxGenEigenspace (μ i)) ∧ ∀ i, ∀ v ∈ S, f i v ∈ S}
  obtain ⟨S, ⟨h0, h1, h2⟩, hmin⟩ := (wellFounded_lt (α := Submodule ℂ W)).has_min A
    ⟨_, (Submodule.ne_bot_iff _).2 ⟨u, hu, fun h => hlu (by rw [h, map_zero])⟩, le_rfl, fun i v hv =>
      (Submodule.mem_iInf _).2 fun j =>
        Module.End.mapsTo_maxGenEigenspace_of_comm (hc j i) (μ j) ((Submodule.mem_iInf _).1 hv j)⟩
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 h0
  refine ⟨v, hv0, fun i => ?_⟩
  have ne : ∀ (m : ℕ), ∀ x ∈ S, x ≠ 0 → ((f i - μ i • 1) ^ m) x = 0 → S ⊓ (f i).eigenspace (μ i) ≠ ⊥ := by
    intro m
    induction m with
    | zero => intro x _ h h'; exact absurd h' h
    | succ m ih =>
      intro x hx h h'
      by_cases e : f i x - μ i • x = 0
      · exact (Submodule.ne_bot_iff _).2 ⟨x, ⟨hx, Module.End.mem_eigenspace_iff.2 (sub_eq_zero.1 e)⟩, h⟩
      · exact ih _ (sub_mem (h2 i x hx) (S.smul_mem _ hx)) e (by rw [pow_succ] at h'; exact h')
  obtain ⟨m, hm⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 ((Submodule.mem_iInf _).1 (h1 hv) i)
  have := hmin (S ⊓ (f i).eigenspace (μ i)) ⟨ne m v hv hv0 hm, inf_le_left.trans h1, fun j x hx =>
    ⟨h2 j x hx.1, Module.End.mem_eigenspace_iff.2 (by
      rw [← Module.End.mul_apply, (hc i j).eq, Module.End.mul_apply, Module.End.mem_eigenspace_iff.1 hx.2, map_smul])⟩⟩
  have e : S ⊓ (f i).eigenspace (μ i) = S := (inf_le_left.lt_or_eq).resolve_left this
  exact Module.End.mem_eigenspace_iff.1 (e.symm ▸ hv : v ∈ S ⊓ (f i).eigenspace (μ i)).2
private theorem ordA_abs {G V : Type} [Group G] (I : Iwa G) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V) (c : ℕ)
    [FiniteDimensional ℂ (fixd π (I.I1 c))] (l : V →ₗ[ℂ] ℂ) (χ : G → ℂ) (hN : ∀ x ∈ I.Nf, ∀ v, l (π x v) = l v)
    (hT : ∀ t ∈ I.Tf, ∀ v, l (π t v) = χ t * l v) {w : V} (hw : w ∈ fixd π (I.I1 c)) (hl : l w ≠ 0) :
    ∃ v ∈ fixd π (I.I1 c), v ≠ 0 ∧ (∀ t ∈ I.T, π t v = χ t • v) ∧
      ∀ a ∈ I.P, I.uOp π a v = (((I.Nconj a).relIndex I.N : ℂ) * χ a) • v := by
  have mul : ∀ (g h : G) (w : V), π g (π h w) = π (g * h) w := fun g h w => by
    rw [map_mul π g h, Module.End.mul_apply]
  have kN : ∀ v : fixd π (I.I1 c), (v : V) ∈ fixd π I.N := fun v x hx =>
    v.2 x (Subgroup.mem_sup_left (Subgroup.mem_sup_left hx))
  have st : ∀ t ∈ I.T, ∀ v ∈ fixd π (I.I1 c), π t v ∈ fixd π (I.I1 c) := by
    intro t ht v hv g hg
    obtain ⟨x, hx, s, hs, y, hy, rfl⟩ := (iwMem G I c g).2.1.1 hg
    have e : x * s * y * t = t * ((t⁻¹ * x * t⁻¹⁻¹) * s * (t⁻¹ * y * t⁻¹⁻¹)) := by
      have := I.comm s (I.T_le (I.Tc_le c hs)) t (I.T_le ht)
      calc x * s * y * t = x * (s * t) * (t⁻¹ * y * t) := by group
        _ = _ := by rw [this]; group
    rw [mul, e, ← mul, hv _ ((iwMem G I c _).2.1.2
      ⟨_, I.T_N _ (inv_mem ht) x hx, s, hs, _, I.T_Nm c _ (inv_mem ht) y hy, rfl⟩)]
  have hJ : I.jacKer π ≤ LinearMap.ker l := Submodule.span_le.2 (by
    rintro _ ⟨x, hx, v, rfl⟩
    simp [hN x hx])
  let f : I.T ⊕ I.P → Module.End ℂ (fixd π (I.I1 c)) :=
    Sum.elim (fun t => (π t).restrict (st t t.2)) fun a => (I.uOp π a).restrict ((uOpLevel G I ℂ V π c).1 a a.2)
  have mix : ∀ t a, Commute (f (.inl t)) (f (.inr a)) := fun t a => LinearMap.ext fun v => Subtype.ext
    ((uOpMul G I ℂ V π a a a.2 a.2 v (kN v)).2.2.2.1 t t.2)
  obtain ⟨v, hv0, hv⟩ := ordA_lin f (by
      rintro (s | a) (t | b)
      · refine LinearMap.ext fun v => Subtype.ext ?_
        show π s (π t v) = π t (π s v)
        rw [mul, mul, I.comm s (I.T_le s.2) t (I.T_le t.2)]
      · exact mix _ _
      · exact (mix _ _).symm
      · refine LinearMap.ext fun v => Subtype.ext ?_
        show I.uOp π a (I.uOp π b v) = I.uOp π b (I.uOp π a v)
        rw [(uOpMul G I ℂ V π a b a.2 b.2 v (kN v)).2.1, (uOpMul G I ℂ V π b a b.2 a.2 v (kN v)).2.1,
          I.comm a (I.P_le a a.2) b (I.P_le b b.2)])
    (l.comp (Submodule.subtype _))
    (Sum.elim (fun t => χ t) fun a => ((I.Nconj a).relIndex I.N : ℂ) * χ a) (by
      rintro (t | a) v
      · exact hT t (I.T_le t.2) v
      · have := hJ (propCp G I ℂ V π a a.2 v (kN v))
        rw [LinearMap.mem_ker, map_sub, map_smul, hT a (I.P_le a a.2), sub_eq_zero, smul_eq_mul, ← mul_assoc] at this
        exact this) (w := ⟨w, hw⟩) hl
  exact ⟨v, v.2, fun h => hv0 (Subtype.ext h), fun t ht => congrArg Subtype.val (hv (.inl ⟨t, ht⟩)),
    fun a ha => congrArg Subtype.val (hv (.inr ⟨a, ha⟩))⟩
section SlopeTestRemainingChoices
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
private theorem exists_torus_eq_diagT_eq_prod_eT_and_mem_Uc_of_mem_Tc (t : (glIwa k n).T) : ∃ y : Fin n → Uo k, (t : GL (Fin n) k) = diagT k (Fin n) (fun i => y i) ∧
    t = (List.ofFn fun i => eT k n i (y i)).prod ∧ ∀ c, (t : GL (Fin n) k) ∈ (glIwa k n).Tc c → ∀ i, (y i : kˣ) ∈ Uc k (c + 1) := by
  obtain ⟨y, h1, h2⟩ := (glBridge k n ℂ (Representation.trivial ℂ _ ℂ)).2.2.2.2.2.2.2.2.2 t
  refine ⟨y, ?_, Subtype.ext ?_, h2⟩
  · rw [h1]
    show (List.ofFn fun i => diagT k (Fin n) (Pi.mulSingle i (y i : kˣ))).prod = _
    rw [show (fun i => diagT k (Fin n) (Pi.mulSingle i (y i : kˣ))) =
      diagT k (Fin n) ∘ fun i => Pi.mulSingle i ((fun i => (y i : kˣ)) i) from rfl,
      ← List.map_ofFn, ← map_list_prod, List.prod_ofFn, Finset.univ_prod_mulSingle]
  · rw [h1]
    exact ((map_list_prod (glData k n).T.subtype _).trans (by rw [List.map_ofFn]; rfl)).symm
private theorem ordA_val (ω : Fin n → kˣ →* ℂˣ) (j : ℕ) (hj : j ≤ n) :
    ((Nat.card 𝓀[k] ^ (j * (n - j)) : ℕ) : ℂ) * ∏ i : Fin n,
      ((absPow k ((modExp (fun _ : Fin n => Unit) i : ℂ) / 2) * (ω i * absPow k (((n : ℂ) - 1) / 2)))
        (unif k ^ (if (i : ℕ) < j then (1 : ℤ) else 0)) : ℂ) = psEig ω j := by
  have hq : nabs k (unif k) = (Nat.card 𝓀[k] : ℝ)⁻¹ := GlobalTheory.GLDoubling.nabs_unif GlAx.unif_spec
  have h0 : (Nat.card 𝓀[k] : ℂ) ≠ 0 := by
    have := nabs_pos' k (unif k)
    rw [hq] at this
    exact_mod_cast (inv_pos.1 this).ne'
  have h1 : ∀ i : Fin n, ((absPow k ((modExp (fun _ : Fin n => Unit) i : ℂ) / 2) * (ω i * absPow k (((n : ℂ) - 1) / 2)))
        (unif k ^ (if (i : ℕ) < j then (1 : ℤ) else 0)) : ℂ) =
      if (i : ℕ) < j then (ω i (unif k) : ℂ) * ((Nat.card 𝓀[k] : ℂ) ^ (n - 1 - i))⁻¹ else 1 := by
    intro i
    split_ifs
    · have e : (modExp (fun _ : Fin n => Unit) i : ℂ) / 2 + ((n : ℂ) - 1) / 2 = ((n - 1 - i : ℕ) : ℂ) := by
        have := i.2
        rw [modExp_fin _ (fun _ => by simp), Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
        push_cast; ring
      rw [mul_left_comm, ← absPow_add, e, zpow_one, MonoidHom.mul_apply, Units.val_mul, val_absPow, hq,
        Complex.cpow_natCast]
      simp
    · simp
  have h2 : ∀ m, m ≤ n → ∑ i ∈ Finset.range m, (n - 1 - i) = m * (n - m) + ∑ i ∈ Finset.range m, i := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      intro hm
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih (by omega)]
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
      rw [show m + 1 + d - m = d + 1 by omega, show m + 1 + d - 1 - m = d by omega, Nat.add_sub_cancel_left]
      ring
  have h3 : ∀ g : ℕ → ℕ, ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < j), g i = ∑ i ∈ Finset.range j, g i := by
    intro g
    rw [Finset.sum_filter, Fin.sum_univ_eq_sum_range (fun i => if i < j then g i else 0), ← Finset.sum_filter]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  simp only [h1]
  rw [← Finset.prod_filter, psEig, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_inv_distrib,
    Finset.prod_inv_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum, h3 fun i => n - 1 - i, h3 fun i => i,
    h2 j hj, pow_add, Nat.cast_pow]
  field_simp
end SlopeTestRemainingChoices
theorem UpperTheory.V.Hi.exists_ne_zero_mem_eig_uOp_eq_psEig_smul_of_equiv_ps :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (ω : Fin n → kˣ →* ℂˣ), Nonempty (π.Equiv (PS ω)) → ∀ c : ℕ, (∀ i, ∀ y ∈ Uc k (c + 1), ω i y = 1) → ∀ φ : (glIwa k n).T →* ℂˣ, IsInvOn φ ω → ∃ v ∈ (glIwa k n).eig π c φ, v ≠ 0 ∧ ∀ j ≤ n, (glIwa k n).uOp π (al k n j) v = psEig ω j • v := by
  intro _ k _ _ _ _ n V _ _ π ω ⟨e⟩ c hω φ hφ
  classical
  obtain ⟨-, -, hI, -, -, -, -, hidx, -⟩ := glBridge k n V π
  let μ : Fin n → kˣ →* ℂˣ := fun i => ω i * absPow k (((n : ℂ) - 1) / 2)
  let Ψ : Levi k (fun _ : Fin n => Unit) →* ℂˣ :=
    deltaHalf k _ * (torusChar μ).comp (leviTorus k (Fin n)).symm.toMonoidHom
  let χ : GL (Fin n) k → ℂ := fun g => if h : g ∈ parab k (points (Fin n)) then Ψ (leviProj k _ ⟨g, h⟩) else 0
  have he : ∀ g v, e.toLinearEquiv (π g v) = PS ω g (e.toLinearEquiv v) := fun g v => e.toIntertwiningMap.isIntertwining _ _ g v
  let l : V →ₗ[ℂ] ℂ :=
    { toFun := fun v => (e.toLinearEquiv v).1.1 1
      map_add' := fun a b => by rw [map_add]; rfl
      map_smul' := fun a b => by rw [map_smul]; rfl }
  let σ := (twist ((ofChar (torusChar μ)).comp (leviTorus k (Fin n)).symm.toMonoidHom) (deltaHalf k _)).comp
    (leviProj k (points (Fin n)))
  have hσ : ∀ p x, σ p x = χ p * x := fun p x => by
    simp only [χ, dif_pos p.2]
    show (deltaHalf k _ _ : ℂ) • ofChar _ _ x = _
    rw [ofChar_apply]
    simp [Ψ, mul_assoc]
  have hl : ∀ g ∈ parab k (points (Fin n)), ∀ v, l (π g v) = χ g * l v := by
    intro g hg v
    refine Eq.trans ?_ (hσ ⟨g, hg⟩ _)
    refine Eq.trans ?_ ((e.toLinearEquiv v).1.2 ⟨g, hg⟩ 1)
    show (e.toLinearEquiv (π g v)).1.1 1 = _
    rw [he, mul_one]
    exact congrArg _ (one_mul g)
  have hN : ∀ x ∈ unipB k (Fin n), χ x = 1 := by
    intro x hx
    have h := unipRad_le_parab k _ hx
    simp only [χ, dif_pos h]
    rw [(coe_mem_unipRad k ⟨x, h⟩).1 hx, map_one, Units.val_one]
  have hD : ∀ t, diagT k (Fin n) t ∈ parab k (points (Fin n)) := fun t => leviEmb_mem_parab k _ _
  have hT : ∀ t, χ (diagT k (Fin n) t) =
      ∏ i, ((absPow k ((modExp (fun _ : Fin n => Unit) i : ℂ) / 2) * μ i) (t i) : ℂ) := by
    intro t
    have hd : ∀ i, Matrix.GeneralLinearGroup.det (leviTorus k (Fin n) t i) = t i :=
      congrFun ((leviTorus k (Fin n)).left_inv t)
    simp only [χ, dif_pos (hD t)]
    rw [show leviProj k _ ⟨_, hD t⟩ = leviTorus k (Fin n) t from leviProj_leviEmb k _ _]
    simp [Ψ, deltaHalf_apply, hd, Finset.prod_mul_distrib]
  have hφ' : ∀ t : (glIwa k n).T, χ t = ((φ t)⁻¹ : ℂˣ) ∧ ((t : GL (Fin n) k) ∈ (glIwa k n).Tc c → χ t = 1) := by
    intro t
    obtain ⟨y, h1, h2, h3⟩ := exists_torus_eq_diagT_eq_prod_eT_and_mem_Uc_of_mem_Tc t
    have h4 : χ t = ∏ i, (ω i (y i) : ℂ) := by
      rw [h1, hT]
      refine Finset.prod_congr rfl fun i _ => ?_
      simp only [μ, MonoidHom.mul_apply, isUnram_absPow k _ _ (y i).2, one_mul, mul_one]
    refine ⟨?_, fun h => by rw [h4]; exact Finset.prod_eq_one fun i _ => by rw [hω i _ (h3 c h i), Units.val_one]⟩
    have h5 : φ t = ∏ i, (ω i (y i))⁻¹ := by
      refine (congrArg φ h2).trans ((map_list_prod φ _).trans ?_)
      refine (congrArg List.prod (List.map_ofFn ..)).trans (List.prod_ofFn.trans ?_)
      exact Finset.prod_congr rfl fun i _ => hφ i (y i)
    rw [h4, h5]
    simp
  have hmul : ∀ a ∈ parab k (points (Fin n)), ∀ b ∈ parab k (points (Fin n)), χ (a * b) = χ a * χ b := by
    intro a ha b hb
    simp only [χ, dif_pos ha, dif_pos hb, dif_pos (mul_mem ha hb)]
    rw [← Units.val_mul, ← map_mul, ← map_mul]
    rfl
  obtain ⟨f, hf1, hf⟩ := UpperTheory.V.Hi.indVec _ ((glIwa k n).I1 c) σ (hI c).1 1 (by
    rintro ⟨p, hp⟩ h
    obtain ⟨x, hx, t, ht, y, hy, rfl⟩ := (iwMem _ _ c p).2.1.1 h
    have hx' := unipRad_le_parab k _ hx.1
    have ht' : t ∈ parab k (points (Fin n)) := by obtain ⟨⟨s, -, rfl⟩, -⟩ := ht; exact hD s
    have hy' : y ∈ parab k (points (Fin n)) := (Subgroup.mul_mem_cancel_left _ (mul_mem hx' ht')).1 hp
    rw [hσ, mul_one]
    show χ (x * t * y) = 1
    rw [hmul _ (mul_mem hx' ht') _ hy', hmul _ hx' _ ht', hN x hx.1, (hφ' ⟨t, ht.1⟩).2 ht,
      hN y ((mem_unipB k).2 ⟨(mem_borel k).1 hy', (GlAx.mem_low.1 hy.1).2⟩), one_mul, one_mul])
  haveI : FiniteDimensional ℂ (GlobalTheory.PRep.fixed (PS ω) ((glIwa k n).I1 c)) :=
    (GlobalTheory.SmGL.ParIndAdm.isAdmissible_parInd _ _).2 _ (hI c).1 (hI c).2
  haveI : FiniteDimensional ℂ (fixd π ((glIwa k n).I1 c)) :=
    Module.Finite.of_injective (e.toLinearEquiv.toLinearMap.restrict (p := fixd π ((glIwa k n).I1 c))
      (q := GlobalTheory.PRep.fixed (PS ω) ((glIwa k n).I1 c)) fun v hv u => by
        show PS ω u (e.toLinearEquiv v) = _
        rw [← he, hv u u.2]; exact (one_smul ℂ _).symm) fun a b h => Subtype.ext (e.toLinearEquiv.injective (congrArg Subtype.val h))
  obtain ⟨v, hv, hv0, h1, h2⟩ := ordA_abs (glIwa k n) π c l χ
    (fun x hx v => by rw [hl x (unipRad_le_parab k _ hx), hN x hx, one_mul])
    (by rintro _ ⟨t, rfl⟩; exact hl _ (hD t)) (w := e.toLinearEquiv.symm f)
    (fun u hu => e.toLinearEquiv.injective (by rw [he, LinearEquiv.apply_symm_apply]; exact hf u hu))
    (by
      show (e.toLinearEquiv (e.toLinearEquiv.symm f)).1.1 1 ≠ 0
      rw [LinearEquiv.apply_symm_apply]
      exact hf1.trans_ne one_ne_zero)
  refine ⟨v, ⟨fun x hx => hv x (Subgroup.mem_sup_left (Subgroup.mem_sup_left hx)),
    fun x hx => hv x (Subgroup.mem_sup_right hx), fun t => by rw [h1 t t.2, (hφ' t).1]⟩, hv0, fun j hj => ?_⟩
  rw [h2 _ (al_mem k n j), hidx j hj, ← ordA_val ω j hj, al, upow, hT]
end
