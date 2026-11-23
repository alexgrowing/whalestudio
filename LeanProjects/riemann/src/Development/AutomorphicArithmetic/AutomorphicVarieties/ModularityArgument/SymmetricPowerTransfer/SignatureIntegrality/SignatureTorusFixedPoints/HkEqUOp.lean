import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.UnitaryHyperbolicOrbitCount
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.LevelTorusLeTorus
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.FinFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.FactJ
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwLeviMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHkApply

noncomputable section

open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Z.Sym.Sig

section Gen

variable {G : Type} [Group G]

private theorem sum_reps {I : Subgroup G} (F : LeviFact I) (a : G) (hI : HeckePair I) (hp : F.Pos a)
    (hn : F.NormJ a) (s : Finset G) (hs : ∀ u ∈ s, u ∈ F.Uf ⊓ I)
    (hs' : ∀ x ∈ F.Uf ⊓ I, ∃! u, u ∈ s ∧ a⁻¹ * (u⁻¹ * x) * a ∈ I)
    {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (ρ : Representation A G M) (v : fixd ρ I) :
    (hk ρ I a v : M) = ∑ u ∈ s, ρ (u * a) v := by
  classical
  obtain ⟨-, h2, -⟩ := hkApply A G M ρ I I a (hI a)
  have hsm : ∀ g : I, g • (a : G ⧸ I) = ((g * a : G) : G ⧸ I) := fun g => rfl
  have hg' : ∀ g ∈ I, ∃ u ∈ F.Uf ⊓ I, ((g * a : G) : G ⧸ I) = ((u * a : G) : G ⧸ I) := by
    intro g hg
    obtain ⟨u, hu, m, hm, l, hl, rfl⟩ := F.fact g hg
    refine ⟨u, hu, ?_⟩
    rw [QuotientGroup.eq]
    have e : (u * m * l * a)⁻¹ * (u * a) = (a⁻¹ * l * a)⁻¹ * (a⁻¹ * m * a)⁻¹ := by group
    rw [e]
    exact I.mul_mem (I.inv_mem (hp.2.2 l hl)) (I.inv_mem (hn m hm).2)
  show (hk2 ρ I I a v : M) = _
  rw [h2 (s.image (· * a)) ?_ ?_ v, Finset.sum_image]
  · intro x _ y _ hxy
    exact mul_right_cancel hxy
  · intro y hy
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hy
    exact ⟨⟨u, (hs u hu).2⟩, hsm _⟩
  · intro q hq
    obtain ⟨⟨g, hg⟩, rfl⟩ := hq
    obtain ⟨u', hu', he⟩ := hg' g hg
    obtain ⟨u, ⟨hus, hui⟩, huniq⟩ := hs' u' hu'
    have hq : ((u * a : G) : G ⧸ I) = ((u' * a : G) : G ⧸ I) := by
      rw [QuotientGroup.eq]
      have e : (u * a)⁻¹ * (u' * a) = a⁻¹ * (u⁻¹ * u') * a := by group
      rw [e]
      exact hui
    refine ⟨u * a, ⟨Finset.mem_image_of_mem _ hus, ?_⟩, ?_⟩
    · show ((u * a : G) : G ⧸ I) = ((g * a : G) : G ⧸ I)
      rw [he, hq]
    · rintro y ⟨hy, hyq⟩
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
      change ((w * a : G) : G ⧸ I) = ((g * a : G) : G ⧸ I) at hyq
      have hw' : w = u := by
        apply huniq w
        refine ⟨hw, ?_⟩
        rw [he] at hyq
        have e : a⁻¹ * (w⁻¹ * u') * a = (w * a)⁻¹ * (u' * a) := by group
        rw [e, ← QuotientGroup.eq]
        exact hyq
      simp [hw']

private theorem hk_eq_uOp (D : Iwa G) {I : Subgroup G} (F : LeviFact I) (a : G) (hI : HeckePair I)
    (hp : F.Pos a) (hn : F.NormJ a) (hU : F.Uf ⊓ I = D.N)
    {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (ρ : Representation A G M) (v : fixd ρ I) :
    (hk ρ I a v : M) = D.uOp ρ a v := by
  classical
  have hNI : ∀ y ∈ D.N, y ∈ F.Uf ⊓ I := fun y hy => hU ▸ hy
  have hND : ∀ y ∈ F.Uf ⊓ I, y ∈ D.N := fun y hy => by rwa [hU] at hy
  have hc : ∀ y : G, y ∈ D.Nconj a ↔ a⁻¹ * y * a ∈ D.N := by
    intro y
    constructor
    · rintro ⟨m, hm, rfl⟩
      have e : a⁻¹ * ((MulAut.conj a).toMonoidHom m) * a = m := by
        simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply]
        group
      rw [e]
      exact hm
    · intro h
      refine ⟨a⁻¹ * y * a, h, ?_⟩
      simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply]
      group
  have heq : ∀ u x : D.N, ((u : ↥D.N ⧸ (D.Nconj a).subgroupOf D.N) = (x : ↥D.N ⧸ (D.Nconj a).subgroupOf D.N)) ↔
      a⁻¹ * ((u : G)⁻¹ * x) * a ∈ I := by
    intro u x
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, hc]
    push_cast
    constructor
    · intro h
      exact (hNI _ h).2
    · intro h
      have hy : (u : G)⁻¹ * x ∈ F.Uf := (hNI _ (D.N.mul_mem (D.N.inv_mem u.2) x.2)).1
      have hm : a⁻¹ * ((u : G)⁻¹ * x) * a ∈ F.Uf ⊓ I :=
        ⟨by simpa using F.M_U a⁻¹ (F.Mf.inv_mem hp.1) _ hy, h⟩
      exact hND _ hm
  have hfin : Finite (↥D.N ⧸ (D.Nconj a).subgroupOf D.N) := by
    have := (hI a).to_subtype
    refine Finite.of_injective (β := MulAction.orbit I (a : G ⧸ I))
      (fun q => ⟨(((Quotient.out q : D.N) : G) * a : G), ⟨⟨_, (hNI _ (Quotient.out q).2).2⟩, rfl⟩⟩) ?_
    intro q q' hqq
    have h1 : (((Quotient.out q : D.N) : G) * a : G ⧸ I) = (((Quotient.out q' : D.N) : G) * a : G ⧸ I) :=
      congrArg Subtype.val hqq
    rw [QuotientGroup.eq] at h1
    have h2 : a⁻¹ * (((Quotient.out q : D.N) : G)⁻¹ * (Quotient.out q' : D.N)) * a ∈ I := by
      have e : a⁻¹ * (((Quotient.out q : D.N) : G)⁻¹ * (Quotient.out q' : D.N)) * a =
          (((Quotient.out q : D.N) : G) * a)⁻¹ * (((Quotient.out q' : D.N) : G) * a) := by group
      rw [e]
      exact h1
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q']
    exact (heq _ _).mpr h2
  haveI := Fintype.ofFinite (↥D.N ⧸ (D.Nconj a).subgroupOf D.N)
  have hinj : Function.Injective (fun q : ↥D.N ⧸ (D.Nconj a).subgroupOf D.N => ((Quotient.out q : D.N) : G)) := by
    intro q q' h
    have h' : Quotient.out q = Quotient.out q' := Subtype.ext h
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', h']
  rw [Iwa.uOp, finsum_eq_sum_of_fintype, LinearMap.sum_apply,
    sum_reps F a hI hp hn
      (Finset.univ.image fun q : ↥D.N ⧸ (D.Nconj a).subgroupOf D.N => ((Quotient.out q : D.N) : G)) ?_ ?_ ρ v]
  · exact Finset.sum_image (f := fun u => ρ (u * a) v) (fun q _ q' _ h => hinj h)
  · intro u hu
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hu
    exact hNI _ (Quotient.out q).2
  · intro x hx0
    have hx := hND x hx0
    set q : ↥D.N ⧸ (D.Nconj a).subgroupOf D.N := ((⟨x, hx⟩ : D.N) : ↥D.N ⧸ (D.Nconj a).subgroupOf D.N) with hqdef
    refine ⟨((Quotient.out q : D.N) : G), ⟨Finset.mem_image_of_mem _ (Finset.mem_univ q), ?_⟩, ?_⟩
    · have := (heq (Quotient.out q) ⟨x, hx⟩).mp (by rw [QuotientGroup.out_eq'])
      simpa using this
    · rintro y ⟨hy, hyI⟩
      obtain ⟨q', -, rfl⟩ := Finset.mem_image.mp hy
      have h3 : (((Quotient.out q' : D.N)) : ↥D.N ⧸ (D.Nconj a).subgroupOf D.N) = q :=
        (heq (Quotient.out q') ⟨x, hx⟩).mpr hyI
      rw [QuotientGroup.out_eq'] at h3
      rw [h3]

end Gen

section Lin

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private def lf (V : Lev k) (n : ℕ) : LeviFact (V.J n) where
  Uf := unipB k (Fin n)
  Mf := (diagT k (Fin n)).range
  Lf := (unipB k (Fin n)).comap (GlobalTheory.CuspRep.invT n k)
  M_U := by
    rintro _ ⟨t, rfl⟩ u hu
    exact GlAx.conj_up t hu
  M_L := by
    rintro _ ⟨t, rfl⟩ l hl
    exact GlAx.conj_low t hl
  uniq := by
    rintro u hu _ ⟨t, rfl⟩ l hl h
    exact GlAx.uniq t hu hl h
  fact g hg := by
    obtain ⟨a, ha, _, ⟨s, hs, rfl⟩, b, hb, rfl⟩ := (factJ k V n).1 g hg
    exact ⟨a, ⟨ha.1, V.N_le ha⟩, diagT k (Fin n) s, ⟨⟨s, rfl⟩, V.dg_mem fun i => hs i trivial⟩, b,
      ⟨hb.1, V.Nm_le hb⟩, rfl⟩

private theorem low_mem (V : Lev k) {l : GL (Fin n) k}
    (h : l ∈ (unipB k (Fin n)).comap (GlobalTheory.CuspRep.invT n k)) (h' : l ∈ V.J n) : l ∈ (glIwa k n).Nm V.c := by
  obtain ⟨a, ha, _, ⟨s, _, rfl⟩, b, hb, rfl⟩ := (factJ k V n).1 _ h'
  have hy : b * (a * diagT k (Fin n) s * b)⁻¹ ∈ (unipB k (Fin n)).comap (GlobalTheory.CuspRep.invT n k) :=
    Subgroup.mul_mem _ hb.1 (Subgroup.inv_mem _ h)
  have key : a * diagT k (Fin n) s * (b * (a * diagT k (Fin n) s * b)⁻¹) = 1 := by group
  obtain ⟨rfl, hs1⟩ := GlAx.uniq s ha.1 hy key
  rw [hs1]
  simpa using hb

private theorem dom_anti {d : Fin n → kˣ} (hd : Dom d) : Antitone fun i => ord k (d i) := by
  intro i j hij
  have h := hd i j hij
  rw [val_ord, val_ord] at h
  have hs : StrictAnti fun m : ℤ => uniformizer k ^ m :=
    zpow_right_strictAnti₀ GlAx.unif_pos uniformizer_lt_one
  exact hs.le_iff_ge.mp h

private theorem pos (V : Lev k) {d : Fin n → kˣ} (hd : Dom d) : (lf V n).Pos (dg d) := by
  have ha : Antitone fun i => ord k (d i) := dom_anti hd
  refine ⟨⟨d, rfl⟩, ?_, ?_⟩
  · rintro u ⟨hu, hJ⟩
    have hN : u ∈ (glData k n).N := ⟨hu, V.J_le_KO hJ⟩
    exact V.N_le (GlAx.conj_N (t := d) (fun i => val_ord (d i)) ha hN)
  · rintro l ⟨hl, hJ⟩
    have hm : l ∈ (glData k n).Nm V.c := low_mem V hl hJ
    have hv : ∀ i, valuation k ↑((d⁻¹) i) = uniformizer k ^ (-ord k (d i)) := by
      intro i
      rw [Pi.inv_apply, Units.val_inv_eq_inv_val, map_inv₀, val_ord, _root_.zpow_neg]
    have hc : ∀ i j : Fin n, j < i → (V.c : ℤ) + -ord k (d j) ≤ V.c + -ord k (d i) := by
      intro i j hji
      have := ha hji.le
      simp only at this
      omega
    have h2 := GlAx.conj_Nm hv hc hm
    have he : diagT k (Fin n) d⁻¹ * l * (diagT k (Fin n) d⁻¹)⁻¹ = (dg d)⁻¹ * l * dg d := by
      simp [dg, map_inv]
    rw [he] at h2
    exact V.Nm_le h2

private theorem normJ (V : Lev k) (d : Fin n → kˣ) : (lf V n).NormJ (dg d) := by
  rintro _ ⟨⟨t, rfl⟩, hj⟩
  have hc : dg d * diagT k (Fin n) t = diagT k (Fin n) t * dg d := by
    show diagT k (Fin n) d * diagT k (Fin n) t = diagT k (Fin n) t * diagT k (Fin n) d
    rw [← map_mul, ← map_mul, mul_comm]
  constructor
  · rw [hc, mul_inv_cancel_right]
    exact hj
  · rw [mul_assoc, ← hc, inv_mul_cancel_left]
    exact hj

end Lin

theorem UpperTheory.V.Z.Sym.Sig.hkMul :
    UpperTheory.V.Z.Sym.Sig.HkMul := by
  intro k _ _ _ _ V n M _ _ ρ
  have hJ : HeckePair (V.J n) := ((finFacts k V).2.2.2.2.2 n).1
  constructor
  · intro d d' hd hd'
    have h := (leviMul ℂ _ M ρ (V.J n) (lf V n) (dg d) (dg d') hJ (pos V hd) (pos V hd')
      (Or.inl (normJ V d))).2
    rw [h]
    congr 1
    exact (map_mul (diagT k (Fin n)) d d').symm
  · intro d hd v
    have hU : (lf V n).Uf ⊓ V.J n = (glIwa k n).N := by
      apply le_antisymm
      · rintro x ⟨hx, hxJ⟩
        exact ⟨hx, V.J_le_KO hxJ⟩
      · intro x hx
        exact ⟨(glIwa k n).N_le hx, V.N_le hx⟩
    exact hk_eq_uOp (glIwa k n) (lf V n) (dg d) hJ (pos V hd) (normJ V d) hU ρ v

end
