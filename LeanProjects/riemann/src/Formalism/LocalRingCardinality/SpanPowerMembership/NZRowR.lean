import Formalism.LocalRingCardinality.SpanPowerMembership.NZRowQ

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Examples₂

variable (D : D7) (c : CentralCharacterOne D)
  (χ0 : Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)) →ₐ[ℂ] ℂ) (h0 : χ0 ⟨D.ntypes.e0, c.cen⟩ = 0)
  (hm : D.R.m ≠ 0) {n : ℕ} {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE]
  [FiniteDimensional ℂ EE] (b : OrthonormalBasis (Fin n) ℂ EE) (a n1 : ℕ) (hn : n ≤ n1) (h1 : n1 ≤ a)

def projSide : RowSide D EE where
  Amb := fun _ => En a
  Mult := fun _ j => MultT EE (En a) j
  instMult := fun _ j => MultT.nacg EE (En a) j
  instMulti := fun _ j => MultT.ips EE (En a) j
  instMultf := fun _ j => MultT.fd EE (En a) j
  multZero := fun _ => LinearIsometryEquiv.refl ℂ EE
  multTop := fun _ => castTop EE (En a) D.R.m hm
  io := fun _ j => ioT (prB b a (hn.trans h1)) j
  Mtilde := fun _ => oB (eb a) _
  cen := fun _ => twoChar c.χ χ0 (eP a n1) (projection_idem a n1)
  eOp := fun _ => eP a n1
  eOp_idem := fun _ => projection_idem a n1
  eOp_sa := fun _ => projection_isSelfAdjoint a n1
  eOp_tie := fun _ => by
    rw [dif_pos c.cen, twoChar_apply, c.one, h0, one_smul, zero_smul, add_zero]
  RR := stdH D.what₂.LL n
  RR_frames := stdH_frames _ n
  jEE := jB D.what₂.embLL b
  jEE_basis := jB_basis _ b
  jEE_norm := jB_norm _ b

local notation "PS" => (projSide D c χ0 h0 hm b a n1 hn h1)

theorem projSide_downTo (μ) (k : ℕ) : (PS).downTo μ (k + 1) = prB b a (hn.trans h1) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show ((PS).downTo μ (k + 1)).comp (LinearMap.id : En a →ₗ[ℂ] En a) = _
    rw [ih]; rfl

theorem projSide_down_cast (μ) : ∀ (j : ℕ) (h : j ≠ 0),
    (PS).downTo μ j ∘ₗ (castTop EE (En a) j h).symm.toLinearEquiv.toLinearMap = prB b a (hn.trans h1)
  | 0, h => absurd rfl h
  | k + 1, _ => by
    rw [projSide_downTo]; rfl

theorem projSide_iota (μ) : (PS).iota μ = prB b a (hn.trans h1) :=
  LinearMap.ext fun x => LinearMap.congr_fun (projSide_down_cast D c χ0 h0 hm b a n1 hn h1 μ D.R.m hm) x

theorem projectionSide_mem_iff (μ) (x : En a) : x ∈ (PS).V0 μ ↔ eP a n1 x = x := by
  constructor
  · rintro ⟨y, rfl⟩
    exact LinearMap.congr_fun (projection_idem a n1) y
  · intro h
    exact ⟨x, h⟩

theorem projSide_sec (μ) : (∀ y, (PS).iota μ (secB b a y) = y) ∧ (∀ y, secB b a y ∈ (PS).V0 μ) ∧
    (∀ y, ∀ u ∈ (PS).Usp μ, inner ℂ u (secB b a y) = 0) ∧
    ∀ y z, inner ℂ (secB b a y) (secB b a z) = inner ℂ y z := by
  refine ⟨fun y => ?_, fun y => (projectionSide_mem_iff D c χ0 h0 hm b a n1 hn h1 μ _).mpr (eP_secB b a n1 hn y),
    fun y u hu => ?_, inner_secB b a (hn.trans h1)⟩
  · rw [projSide_iota]; exact prB_secB b a _ y
  · have h2 : (PS).iota μ u = 0 := hu.2
    rw [projSide_iota] at h2
    exact inner_secB_of_ker b a _ h2 y

theorem projSide_Usp_ne (μ) (hlt : n < n1) : (PS).Usp μ ≠ ⊥ := by
  intro hb
  have hi : n < a := lt_of_lt_of_le hlt h1
  have hmem : eb a ⟨n, hi⟩ ∈ (PS).Usp μ := by
    refine ⟨(projectionSide_mem_iff D c χ0 h0 hm b a n1 hn h1 μ _).mpr ?_, ?_⟩
    · ext i
      rw [eP_apply]
      by_cases h : (i : ℕ) < n1
      · rw [if_pos h]
      · rw [if_neg h]
        have : i ≠ ⟨n, hi⟩ := fun e => h (by rw [e]; exact hlt)
        simp [this]
    · show (PS).iota μ (eb a ⟨n, hi⟩) = 0
      rw [projSide_iota]
      show ∑ k : Fin n, (eb a ⟨n, hi⟩) (Fin.castLE _ k) • b k = 0
      refine Finset.sum_eq_zero fun k _ => ?_
      have : (Fin.castLE (hn.trans h1) k : Fin a) ≠ ⟨n, hi⟩ := fun e => by
        have := congrArg Fin.val e
        simp at this
        omega
      simp [this]
  rw [hb] at hmem
  have hz : eb a ⟨n, hi⟩ = 0 := (Submodule.mem_bot ℂ).mp hmem
  exact (eb a).toBasis.ne_zero ⟨n, hi⟩ (by simpa using hz)

theorem projSide_eOp_ne (μ) (hlt : n1 < a) : (PS).eOp μ ≠ LinearMap.id := by
  intro h
  have h' : eP a n1 = LinearMap.id := h
  have h2 := congrArg (fun f : En a →ₗ[ℂ] En a => f (eb a ⟨n1, hlt⟩) ⟨n1, hlt⟩) h'
  simp [eP_apply] at h2

variable (hO : OFull D)

omit [FiniteDimensional ℂ EE] in

theorem img_lemma {K : Type} [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ)
    {O : Type} [CommRing O] (f : O →+* K) (hf : ∀ z : K, (∃ y, f y = z) ↔ ∃ c : 𝓞 K, z = (c : K))
    (h : n ≤ a) (Vs : Set (En a)) (hV : ∀ y, secB b a y ∈ Vs) (y : Fin n → K) :
    jB σ b y ∈ prB b a h '' ((oB (eb a) (σ.comp f)).carrier ∩ Vs) ↔ y ∈ (stdH K n).L := by
  rw [mem_stdL]
  constructor
  · rintro ⟨x, ⟨hx, -⟩, e⟩ k
    obtain ⟨cx, rfl⟩ := (mem_oB (eb a) _ x).mp hx
    refine (hf (y k)).mp ⟨cx (Fin.castLE h k), σ.injective ?_⟩
    have h2 := congrArg (fun z => b.repr z k) e
    rw [sum_smul_eb] at h2
    have h3 : prB b a h (WithLp.toLp 2 fun i => (σ.comp f) (cx i)) =
        jB σ b (fun k => f (cx (Fin.castLE h k))) := rfl
    simp only [h3, repr_jB] at h2
    exact h2
  · intro hy
    have h' := fun k => (hf (y k)).mpr (hy k)
    choose cy hcy using h'
    refine ⟨secB b a (jB σ b y), ⟨(mem_oB (eb a) _ _).mpr
      ⟨fun i => if hi : (i : ℕ) < n then cy ⟨i, hi⟩ else 0, ?_⟩, hV _⟩, prB_secB b a _ _⟩
    rw [sum_smul_eb]
    ext i
    rw [secB_apply]
    by_cases hi : (i : ℕ) < n
    · simp only [dif_pos hi, repr_jB, RingHom.comp_apply, hcy]
    · simp [dif_neg hi]

include hO in

theorem projSide_rrDef : (PS).RRDef := by
  refine rrDef_of _ (stdH D.what₂.LL n).L (fun w y => ?_) rfl
  rw [RRset_gen, projSide_iota]
  exact img_lemma b a D.what₂.embLL D.what₂.OtoLL hO (hn.trans h1) _
    (fun z => (projectionSide_mem_iff D c χ0 h0 hm b a n1 hn h1 _ _).mpr (eP_secB b a n1 hn z)) y

theorem projSide_rrFull : (PS).RRFull := (stdH_good D.what₂.LL n).2

def projSide_amb : AmbForm D PS := ambOf D _ (fun _ => a) (fun _ => eb a) (fun _ => rfl)

theorem projectionSide_latticeBound (ty : Fin n → D.what₂.FT) (hl : ∀ μ j π, D.what₂.lamP μ j π = 1) : (PS).RowLatticeBoundForBasis b ty 1 := by
  refine ⟨fun μ => ?_, one_pos, fun _ => 1, rfl, fun _ => one_pos, Formalism.BasicNotions.DV.rhoUnit_one D, fun μ σ => ?_⟩
  · obtain ⟨s1, s2, s3, -⟩ := projSide_sec D c χ0 h0 hm b a n1 hn h1 μ
    exact iotaQ_bij' (PS) (μ := μ) (secB b a) s1 s2 s3
  · obtain ⟨s1, s2, s3, s4⟩ := projSide_sec D c χ0 h0 hm b a n1 hn h1 μ
    have hadj := iotaQ_adj' (PS) (μ := μ) (secB b a) s1 s2 s3 s4
    have hp : ((1 * 1 * ∏ j ∈ Finset.Icc 1 D.R.m, D.what₂.lamP μ j (ty σ) : ℝ) : ℂ) = 1 := by simp [hl]
    rw [hadj, hp, one_smul]
    rfl

end Formalism.BasicNotions.Examples₂.NZ
