import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusSubOneWittTensorLatticeSurjectiveFixedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniqueCocycleStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGammaLayerPadicCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeakTopologyWittTiltTensorStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

namespace GlobalTheory.HerrClassMaps

section Core

variable {l : ℕ} [Fact l.Prime] {G LL O V M : Type} [Group G] [TopologicalSpace G] [Field LL] [CommRing O]
  [Algebra O LL] [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
  [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V] {ρ : Representation LL G V}
  [AddCommGroup M] [Module O M]

def Fits (L : Formalism.WeaklyAdmissibleFiltrations.Lattice (O := O) ρ) (j : ↥L.T →ₗ[O] M) (a : G → M →ₗ[O] M)
    (lam : G →* Multiplicative ℤ_[l]) (b z : M) (c : ↥(latticeCocycles L)) : Prop :=
  ∀ (g : G) (t : ↥L.T), (t : V) = (c : G → V) g →
    (lam g = 1 → j t = -(a g b - b)) ∧ (lam g = Multiplicative.ofAdd 1 → j t = z - (a g b - b))

theorem mem_T {L : Formalism.WeaklyAdmissibleFiltrations.Lattice (O := O) ρ} (c : ↥(latticeCocycles L)) (g : G) : (c : G → V) g ∈ L.T :=
  c.2.2 g (Set.mem_univ _)

theorem fits_iff {L : Formalism.WeaklyAdmissibleFiltrations.Lattice (O := O) ρ} {j : ↥L.T →ₗ[O] M} {a : G → M →ₗ[O] M}
    {lam : G →* Multiplicative ℤ_[l]} {b z : M} {c : ↥(latticeCocycles L)} :
    Fits L j a lam b z c ↔ ∀ g, (lam g = 1 → j ⟨_, mem_T c g⟩ = -(a g b - b)) ∧
      (lam g = Multiplicative.ofAdd 1 → j ⟨_, mem_T c g⟩ = z - (a g b - b)) := by
  refine ⟨fun h g => h g _ rfl, fun h g t ht => ?_⟩
  have : t = ⟨_, mem_T c g⟩ := Subtype.ext ht
  rw [this]; exact h g

variable [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [T2Space M]

theorem existsUnique_fits (L : Formalism.WeaklyAdmissibleFiltrations.Lattice (O := O) ρ) (j : ↥L.T →ₗ[O] M) (a : G → M →ₗ[O] M)
    (lam : G →* Multiplicative ℤ_[l]) (g₀ : G)
    (a1 : ∀ x, a 1 x = x) (amul : ∀ g h x, a (g * h) x = a g (a h x))
    (acont : Continuous (fun p : G × M => a p.1 p.2))
    (jemb : Topology.IsEmbedding j) (hc : CompactSpace ↥L.T)
    (hU : ∀ U ∈ nhds (0 : ↥L.T), ∃ k : ℕ, ∀ t : ↥L.T, l ^ k • t ∈ U)
    (ja : ∀ g (t : ↥L.T), a g (j t) = j ⟨ρ g t, L.stable g t t.2⟩)
    (lcont : Continuous lam) (h₀ : lam g₀ = Multiplicative.ofAdd 1) (b z : M)
    (hb : ∀ h, lam h = 1 → a h z = z ∧ ∃ t, j t = a h b - b) (hz : ∃ t, j t = z - (a g₀ b - b)) :
    ∃! c : ↥(latticeCocycles L), Fits L j a lam b z c := by
  obtain ⟨c, ⟨cc, cT, ccoc, c1, c2⟩, cu⟩ := GlobalTheory.T.exists_unique_cocycle_alt l G M (fun g => (a g).toAddMonoidHom) a1 amul acont
    j.toAddMonoidHom.range (by
      have : (j.toAddMonoidHom.range : Set M) = Set.range j := by ext; simp
      rw [this]; exact isCompact_range jemb.continuous)
    (by rintro g _ ⟨t, rfl⟩; exact ⟨_, (ja g t).symm⟩)
    (by
      intro U hU0
      have h0 : j ⁻¹' U ∈ nhds (0 : ↥L.T) :=
        jemb.continuous.continuousAt.preimage_mem_nhds (by simpa using hU0)
      obtain ⟨k, hk⟩ := hU _ h0
      refine ⟨k, ?_⟩
      rintro _ ⟨t, rfl⟩
      have := hk t
      rw [Set.mem_preimage, map_nsmul] at this
      exact this)
    lam g₀ lcont h₀ b z hb hz
  choose d hd using cT
  replace hd : ∀ g, j (d g) = c g := hd
  have dc : Continuous d := by
    rw [jemb.continuous_iff]
    have : j ∘ d = c := funext hd
    rw [this]; exact cc
  have dmem : (fun g => (d g : V)) ∈ latticeCocycles L := by
    refine ⟨⟨continuous_subtype_val.comp dc, fun g h => ?_⟩, fun g _ => (d g).2⟩
    have : d (g * h) = d g + ⟨ρ g (d h), L.stable g _ (d h).2⟩ := by
      apply jemb.injective
      rw [map_add, ← ja, hd, hd, hd]
      exact ccoc g h
    exact congrArg Subtype.val this
  refine ⟨⟨_, dmem⟩, fits_iff.2 fun g => ⟨fun h => (hd g).trans (c1 g h), fun h => (hd g).trans (c2 g h)⟩, ?_⟩
  intro e he
  rw [fits_iff] at he
  have := cu (fun g => j ⟨_, mem_T e g⟩) ⟨jemb.continuous.comp (Continuous.subtype_mk e.2.1.1 _),
    fun g => ⟨_, rfl⟩, fun g h => by
      change j _ = j _ + a g (j _)
      rw [ja, ← map_add]
      congr 1
      exact Subtype.ext (e.2.1.2 g h), fun g h => (he g).1 h, fun g h => (he g).2 h⟩
  apply Subtype.ext
  funext g
  have h2 : j ⟨_, mem_T e g⟩ = j (d g) := (congrFun this g).trans (hd g).symm
  exact congrArg Subtype.val (jemb.injective h2)

omit [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [T2Space M] in
theorem exists_class (L : Formalism.WeaklyAdmissibleFiltrations.Lattice (O := O) ρ) (j : ↥L.T →ₗ[O] M) (a : G → M →ₗ[O] M)
    (lam : G →* Multiplicative ℤ_[l]) (φ : M →ₗ[O] M)
    (hρ : ∀ x, Continuous fun g => ρ g x)
    (ja : ∀ g (t : ↥L.T), a g (j t) = j ⟨ρ g t, L.stable g t t.2⟩)
    (onto : ∀ y, ∃ b, φ b - b = y) (ker : ∀ b, φ b = b → ∃ t, b = j t)
    {Z : Type} [AddCommGroup Z] [Module O Z] (y z : Z →ₗ[O] M)
    (eu : ∀ p b, φ b - b = y p → ∃! c : ↥(latticeCocycles L), Fits L j a lam b (z p) c) :
    ∃ cl : Z →ₗ[O] LatticeCohomology L, ∀ p b c, φ b - b = y p → Fits L j a lam b (z p) c →
      Submodule.Quotient.mk c = cl p := by
  let W : Submodule O (Z × M × ↥(latticeCocycles L)) :=
    { carrier := {w | φ w.2.1 - w.2.1 = y w.1 ∧ Fits L j a lam w.2.1 (z w.1) w.2.2}
      zero_mem' := ⟨by simp, fits_iff.2 fun g => by
        change (_ → j 0 = _) ∧ (_ → j 0 = _)
        simp⟩
      add_mem' := by
        rintro u w ⟨hu, hu'⟩ ⟨hw, hw'⟩
        rw [fits_iff] at hu' hw'
        refine ⟨by simp only [Prod.snd_add, Prod.fst_add, map_add, ← hu, ← hw]; abel, fits_iff.2 fun g => ?_⟩
        have : (⟨_, mem_T (u + w).2.2 g⟩ : ↥L.T) = ⟨_, mem_T u.2.2 g⟩ + ⟨_, mem_T w.2.2 g⟩ := rfl
        rw [this, map_add]
        constructor
        · intro h
          rw [(hu' g).1 h, (hw' g).1 h]
          simp only [Prod.snd_add, Prod.fst_add, map_add]; abel
        · intro h
          rw [(hu' g).2 h, (hw' g).2 h]
          simp only [Prod.snd_add, Prod.fst_add, map_add]; abel
      smul_mem' := by
        rintro r u ⟨hu, hu'⟩
        rw [fits_iff] at hu'
        refine ⟨by simp only [Prod.smul_snd, Prod.smul_fst, map_smul, ← hu, smul_sub], fits_iff.2 fun g => ?_⟩
        have : (⟨_, mem_T (r • u).2.2 g⟩ : ↥L.T) = r • ⟨_, mem_T u.2.2 g⟩ := rfl
        rw [this, map_smul]
        constructor
        · intro h
          rw [(hu' g).1 h]
          simp only [Prod.smul_snd, Prod.smul_fst, map_smul, smul_sub, smul_neg]
        · intro h
          rw [(hu' g).2 h]
          simp only [Prod.smul_snd, Prod.smul_fst, map_smul, smul_sub, smul_neg] }
  let π : ↥W →ₗ[O] Z := (LinearMap.fst O _ _).comp W.subtype
  let κ : ↥W →ₗ[O] LatticeCohomology L := (Submodule.mkQ _).comp
    ((LinearMap.snd O _ _).comp ((LinearMap.snd O _ _).comp W.subtype))
  have πs : Function.Surjective π := by
    intro p
    obtain ⟨b, hb⟩ := onto (y p)
    obtain ⟨c, hc, -⟩ := eu p b hb
    exact ⟨⟨(p, b, c), hb, hc⟩, rfl⟩
  have hk : LinearMap.ker π ≤ LinearMap.ker κ := by
    rintro ⟨⟨p, b, c⟩, hb, hc⟩ hp
    obtain rfl : p = 0 := hp
    change φ b - b = y 0 at hb
    change Fits L j a lam b (z 0) c at hc
    obtain ⟨t, rfl⟩ := ker b (by rw [map_zero, sub_eq_zero] at hb; exact hb)
    have emem : cob ρ (-(t : V)) ∈ latticeCocycles L := by
      refine ⟨⟨?_, fun g h => ?_⟩, fun g _ => ?_⟩
      · refine ((hρ (-(t : V))).add (continuous_const (y := (t : V)))).congr fun g => ?_
        simp [cob]
      · simp [cob]; abel
      · exact L.T.sub_mem (L.stable g _ (L.T.neg_mem t.2)) (L.T.neg_mem t.2)
    have he : Fits L j a lam (j t) (z 0) ⟨_, emem⟩ := by
      intro g u hu
      have : u = -(⟨ρ g t, L.stable g t t.2⟩ - t) := by
        apply Subtype.ext
        rw [hu]; simp [cob]; abel
      rw [this, map_neg, map_sub, ← ja, map_zero, zero_sub]
      exact ⟨fun _ => rfl, fun _ => rfl⟩
    have := (eu 0 _ hb).unique hc he
    subst this
    change Submodule.Quotient.mk _ = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact ⟨-(t : V), L.T.neg_mem t.2, rfl⟩
  refine ⟨((LinearMap.ker π).liftQ κ hk).comp (π.quotKerEquivOfSurjective πs).symm.toLinearMap, ?_⟩
  intro p b c hb hc
  have : (π.quotKerEquivOfSurjective πs).symm p = Submodule.Quotient.mk ⟨(p, b, c), hb, hc⟩ := by
    rw [LinearEquiv.symm_apply_eq]; rfl
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, this, Submodule.liftQ_apply]
  rfl

end Core

section Tensor

variable {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL] [Algebra Qp LL]
  [CommRing O] [Algebra O LL] [TopologicalSpace LL] {R : Type} [CommRing R] [Algebra O R]

theorem TWact_one (f : R →ₐ[O] R) (hf : ∀ r, f r = r) (T : LocLat G Qp LL O) (x : TW R T) :
    TWact f T 1 x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul r t =>
    have : T.actT 1 t = t := Subtype.ext (by simp [LocLat.actT])
    simp [TWact, hf, this]

theorem TWact_mul (f f₁ f₂ : R →ₐ[O] R) (hf : ∀ r, f r = f₁ (f₂ r)) (T : LocLat G Qp LL O) (g h : G)
    (x : TW R T) : TWact f T (g * h) x = TWact f₁ T g (TWact f₂ T h x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul r t =>
    have : T.actT (g * h) t = T.actT g (T.actT h t) :=
      Subtype.ext (show T.ρ (g * h) t = T.ρ g (T.ρ h t) by simp)
    simp [TWact, hf, this]

theorem TWmap_act (φ f : R →ₐ[O] R) (hf : ∀ r, φ (f r) = f (φ r)) (T : LocLat G Qp LL O) (g : G)
    (x : TW R T) : TWmap φ T (TWact f T g x) = TWact f T g (TWmap φ T x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul r t => simp [TWact, TWmap, hf]

theorem TWact_one_tmul (f : R →ₐ[O] R) (T : LocLat G Qp LL O) (g : G) (t : ↥T.L.T) :
    TWact f T g ((1 : R) ⊗ₜ[O] t) = (1 : R) ⊗ₜ[O] (⟨T.ρ g t, T.L.stable g t t.2⟩ : ↥T.L.T) := by
  simp only [TWact, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, map_one]
  rfl

end Tensor

theorem fixed_one {O M : Type} [CommRing O] [AddCommGroup M] [Module O M] (φ a : M →ₗ[O] M)
    (h : ∀ x, φ (a x) = a (φ x)) (b y : M) (hb : φ b - b = y) (hy : a y = y) :
    φ (a b - b) = a b - b := by
  have : φ b = y + b := by rw [← hb]; abel
  rw [map_sub, h, this, map_add, hy]; abel

theorem fixed_two {O M : Type} [CommRing O] [AddCommGroup M] [Module O M] (φ a : M →ₗ[O] M)
    (h : ∀ x, φ (a x) = a (φ x)) (b y z : M) (hb : φ b - b = y) (hy : a y - y = φ z - z) :
    φ (z - (a b - b)) = z - (a b - b) := by
  have h1 : φ b = y + b := by rw [← hb]; abel
  have h2 : φ z = a y - y + z := by rw [hy]; abel
  rw [map_sub, map_sub, h, h1, h2, map_add]; abel

theorem herr_eq {O D : Type} [CommRing O] [AddCommGroup D] [Module O D] {γ φ : D →ₗ[O] D} {p : D × D}
    (h : p ∈ herrCocycles γ φ) : γ p.1 - p.1 = φ p.2 - p.2 := by
  have h' : (γ p.1 - p.1) + -(φ p.2 - p.2) = 0 := h
  rwa [add_neg_eq_zero] at h'

theorem herrΔ_fix {O D ι : Type} [CommRing O] [AddCommGroup D] [Module O D] {γ φ : D →ₗ[O] D}
    {S : Finset ι} {δ : ι → D →ₗ[O] D} {p : D × D} (h : p ∈ herrZ1Δ γ φ S δ) {d : ι} (hd : d ∈ S) :
    δ d p.1 = p.1 ∧ δ d p.2 = p.2 := by
  have h2 := h.2
  simp only [SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at h2
  have := h2 d hd
  exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩

section Generic

variable {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
  [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] {RW : Type} [CommRing RW] [Algebra O RW]
  (φR : RW →ₐ[O] RW) (gR : G → (RW →ₐ[O] RW))

def Setup (l : ℕ) (T : LocLat G Qp LL O) : Prop :=
  ((∀ y : TW RW T, ∃ b, TWmap φR T b - b = y) ∧
    (∀ b : TW RW T, TWmap φR T b = b → ∃ t : ↥T.L.T, b = (1 : RW) ⊗ₜ[O] t)) ∧
  ∃ τ : TopologicalSpace (TW RW T), letI := τ; T2Space (TW RW T) ∧ IsTopologicalAddGroup (TW RW T) ∧
    Continuous (fun p : G × TW RW T => TWact (gR p.1) T p.1 p.2) ∧
    Topology.IsEmbedding (fun t : ↥T.L.T => (1 : RW) ⊗ₜ[O] t) ∧ CompactSpace ↥T.L.T ∧
    ∀ U ∈ nhds (0 : ↥T.L.T), ∃ k : ℕ, ∀ t : ↥T.L.T, l ^ k • t ∈ U

abbrev jT (RW : Type) [CommRing RW] [Algebra O RW] (T : LocLat G Qp LL O) : ↥T.L.T →ₗ[O] TW RW T :=
  TensorProduct.mk O RW ↥T.L.T 1

variable {φR gR} [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

theorem eu_full (g1 : ∀ r, gR 1 r = r) (gmul : ∀ g h r, gR (g * h) r = gR g (gR h r))
    (gφ : ∀ g r, φR (gR g r) = gR g (φR r))
    (T : LocLat G Qp LL O) (hT : Setup φR gR l T) (lam : G →* Multiplicative ℤ_[l])
    (g₀ : G) (lcont : Continuous lam) (h₀ : lam g₀ = Multiplicative.ofAdd 1) (b y z : TW RW T)
    (hb : TWmap φR T b - b = y) (hfix : ∀ h, lam h = 1 → TWact (gR h) T h y = y ∧ TWact (gR h) T h z = z)
    (hz : TWact (gR g₀) T g₀ y - y = TWmap φR T z - z) :
    ∃! c : ↥(latticeCocycles T.L), Fits T.L (jT RW T) (fun g => TWact (gR g) T g) lam b z c := by
  obtain ⟨⟨-, hker⟩, τ, h1, h2, h3, h4, h5, h6⟩ := hT
  let _ := τ
  have comm : ∀ g x, TWmap φR T (TWact (gR g) T g x) = TWact (gR g) T g (TWmap φR T x) :=
    fun g x => TWmap_act _ _ (gφ g) T g x
  refine existsUnique_fits T.L (jT RW T) (fun g => TWact (gR g) T g) lam g₀ (TWact_one _ g1 T)
    (fun g h => TWact_mul _ _ _ (gmul _ _) T g h) h3 h4 h5 h6
    (fun g t => TWact_one_tmul _ T g t) lcont h₀ b z (fun h hh => ⟨(hfix h hh).2, ?_⟩) ?_
  · obtain ⟨t, ht⟩ := hker _ (fixed_one _ _ (comm h) b y hb (hfix h hh).1)
    exact ⟨t, ht.symm⟩
  · obtain ⟨t, ht⟩ := hker _ (fixed_two _ _ (comm g₀) b y z hb hz)
    exact ⟨t, ht.symm⟩

theorem eu_res (g1 : ∀ r, gR 1 r = r) (gmul : ∀ g h r, gR (g * h) r = gR g (gR h r))
    (gφ : ∀ g r, φR (gR g r) = gR g (φR r))
    (T : LocLat G Qp LL O) (hT : Setup φR gR l T) (S : Subgroup G)
    (hS : IsClosed (S : Set G)) (lam : ↥S →* Multiplicative ℤ_[l])
    (g₀ : ↥S) (lcont : Continuous lam) (h₀ : lam g₀ = Multiplicative.ofAdd 1) (b y z : TW RW T)
    (hb : TWmap φR T b - b = y)
    (hfix : ∀ h : ↥S, lam h = 1 → TWact (gR h) T (h : G) y = y ∧ TWact (gR h) T (h : G) z = z)
    (hz : TWact (gR g₀) T (g₀ : G) y - y = TWmap φR T z - z) :
    ∃! c : ↥(latticeCocycles (resLat T S)),
      Fits (resLat T S) (jT RW T) (fun g => TWact (gR g) T (g : G)) lam b z c := by
  obtain ⟨⟨-, hker⟩, τ, h1, h2, h3, h4, h5, h6⟩ := hT
  let _ := τ
  have : CompactSpace ↥S := isCompact_iff_compactSpace.1 hS.isCompact
  have comm : ∀ g x, TWmap φR T (TWact (gR g) T g x) = TWact (gR g) T g (TWmap φR T x) :=
    fun g x => TWmap_act _ _ (gφ g) T g x
  have hf : Continuous (fun p : ↥S × TW RW T => ((p.1 : G), p.2)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have h3' : Continuous (fun p : ↥S × TW RW T => TWact (gR p.1) T (p.1 : G) p.2) := by
    have := h3.comp hf
    simpa only [Function.comp_def] using this
  refine existsUnique_fits (resLat T S) (jT RW T) (fun g => TWact (gR g) T (g : G)) lam g₀
    (fun x => TWact_one (gR 1) g1 T x)
    (fun g h x => TWact_mul (gR (g * h)) (gR g) (gR h) (gmul g h) T (g : G) (h : G) x)
    h3' h4 h5 h6
    (fun g t => TWact_one_tmul _ T (g : G) t) lcont h₀ b z (fun h hh => ⟨(hfix h hh).2, ?_⟩) ?_
  · obtain ⟨t, ht⟩ := hker _ (fixed_one _ _ (comm h) b y hb (hfix h hh).1)
    exact ⟨t, ht.symm⟩
  · obtain ⟨t, ht⟩ := hker _ (fixed_two _ _ (comm g₀) b y z hb hz)
    exact ⟨t, ht.symm⟩

variable {K₀ K : Type} [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {v : AddValuation LL (WithTop ℚ)} {n s : ℕ}
    {Γ : WGam PD LL O v n s} {R : WSer Γ} {RA : Type} [CommRing RA] [Algebra O RA]
    {inclR : RA →ₐ[O] RW} {πA : RA} {I : WIo R RA RW inclR φR gR πA}

theorem nonempty_cl (g1 : ∀ r, gR 1 r = r) (gmul : ∀ g h r, gR (g * h) r = gR g (gR h r))
    (gφ : ∀ g r, φR (gR g r) = gR g (φR r)) (hT : ∀ T : LocLat G Qp LL O, Setup φR gR l T)
    (hlam : (∃ lam : ↥Γ.GKs →* Multiplicative ℤ_[l], Continuous lam ∧ (∀ g, lam g = 1 ↔ Γ.resΓ (g : G) = 1) ∧
      (∀ g, lam g = Multiplicative.ofAdd 1 ↔ Γ.resΓ (g : G) = Γ.gam) ∧ (∃ g, lam g = Multiplicative.ofAdd 1) ∧
      IsClosed (Γ.GKs : Set G)) ∧ ∃ lam : G →* Multiplicative ℤ_[l], Continuous lam ∧
      (∀ g, lam g = 1 ↔ Γ.resΓ g ∈ Γ.DelF) ∧ (∀ g, Γ.resΓ g = Γ.gamK → lam g = Multiplicative.ofAdd 1))
    (E : WEt I) : Nonempty (WCl E) := by
  obtain ⟨⟨lam, lc, l1, l2, ⟨g₀, hg₀⟩, hS⟩, mu, mc, m1, m2⟩ := hlam
  obtain ⟨g₁, hg₁⟩ := Γ.resΓ_onto Γ.gamK
  have eu₁ : ∀ T (p : ↥(herrCocycles (E.γD T Γ.gam) (E.φD T))) b,
      TWmap φR T b - b = E.jD T (p : E.DD T × E.DD T).1 →
      ∃! c : ↥(latticeCocycles (resLat T Γ.GKs)), Fits (resLat T Γ.GKs) (jT RW T) (fun g => TWact (gR g) T (g : G)) lam b
        (E.jD T (p : E.DD T × E.DD T).2) c := by
    intro T p b hb
    refine eu_res g1 gmul gφ T (hT T) _ hS lam g₀ lc hg₀ b _ _ hb (fun h hh => ?_) ?_
    · rw [← E.jD_act, ← E.jD_act, (l1 h).1 hh, E.γD_one, E.γD_one]
      exact ⟨rfl, rfl⟩
    · rw [← E.jD_act, ← E.jD_φ, (l2 g₀).1 hg₀, ← map_sub, ← map_sub, herr_eq p.2]
  have eu₂ : ∀ T (p : ↥(herrZ1Δ (E.γD T Γ.gamK) (E.φD T) Γ.DelF (E.γD T))) b,
      TWmap φR T b - b = E.jD T (p : E.DD T × E.DD T).1 →
      ∃! c : ↥(latticeCocycles T.L), Fits T.L (jT RW T) (fun g => TWact (gR g) T g) mu b
        (E.jD T (p : E.DD T × E.DD T).2) c := by
    intro T p b hb
    refine eu_full g1 gmul gφ T (hT T) mu g₁ mc (m2 _ hg₁) b _ _ hb (fun h hh => ?_) ?_
    · have := herrΔ_fix p.2 ((m1 h).1 hh)
      rw [← E.jD_act, ← E.jD_act, this.1, this.2]
      exact ⟨rfl, rfl⟩
    · rw [← E.jD_act, ← E.jD_φ, hg₁, ← map_sub, ← map_sub, herr_eq p.2.1]
  have ex₁ := fun T : LocLat G Qp LL O => exists_class (resLat T Γ.GKs) (jT RW T)
    (fun g => TWact (gR g) T (g : G)) lam (TWmap φR T)
    (fun x => (T.cont x).comp continuous_subtype_val) (fun g t => TWact_one_tmul _ T (g : G) t)
    (hT T).1.1 (hT T).1.2
    ((E.jD T).comp ((LinearMap.fst O _ _).comp (herrCocycles (E.γD T Γ.gam) (E.φD T)).subtype))
    ((E.jD T).comp ((LinearMap.snd O _ _).comp (herrCocycles (E.γD T Γ.gam) (E.φD T)).subtype)) (eu₁ T)
  have ex₂ := fun T : LocLat G Qp LL O => exists_class T.L (jT RW T)
    (fun g => TWact (gR g) T g) mu (TWmap φR T)
    T.cont (fun g t => TWact_one_tmul _ T g t)
    (hT T).1.1 (hT T).1.2
    ((E.jD T).comp ((LinearMap.fst O _ _).comp (herrZ1Δ (E.γD T Γ.gamK) (E.φD T) Γ.DelF (E.γD T)).subtype))
    ((E.jD T).comp ((LinearMap.snd O _ _).comp (herrZ1Δ (E.γD T Γ.gamK) (E.φD T) Γ.DelF (E.γD T)).subtype))
    (eu₂ T)
  choose cl hcl using ex₁
  choose clK hclK using ex₂
  refine ⟨⟨cl, clK, fun hγ T pr pr' hp => ?_, fun T pr b hb => ?_, fun _ T pr b hb => ?_⟩⟩
  · obtain ⟨b, hb⟩ := (hT T).1.1 (E.jD T (pr : E.DD T × E.DD T).1)
    obtain ⟨c, hc, -⟩ := eu₂ T pr b hb
    rw [← hclK T pr b c hb hc]
    refine hcl T pr' b ⟨_, resFun_Z1T T Γ.GKs c c.2⟩ (hb.trans (congrArg (fun q => E.jD T q.1) hp.symm)) ?_
    intro g t ht
    have := hc g t ht
    refine ⟨fun h => this.1 ((m1 _).2 ?_), fun h => (this.2 (m2 _ ?_)).trans ?_⟩
    · rw [(l1 g).1 h, Γ.DelF_def]
      exact ⟨1, one_pos, one_pow _⟩
    · rw [(l2 g).1 h, hγ]
    · rw [← hp]; rfl
  · obtain ⟨c, hc, -⟩ := eu₁ T pr b hb
    exact ⟨c, hcl T pr b c hb hc, fun g t ht =>
      ⟨fun h => (hc g t ht).1 ((l1 g).2 h), fun h => (hc g t ht).2 ((l2 g).2 h)⟩⟩
  · obtain ⟨c, hc, -⟩ := eu₂ T pr b hb
    exact ⟨c, hclK T pr b c hb hc, fun g t ht =>
      ⟨fun h => (hc g t ht).1 ((m1 g).2 h), fun h => (hc g t ht).2 (m2 g h)⟩⟩

end Generic

theorem map_id_comm {Z O W : Type} [CommRing Z] [CommRing O] [CommRing W] [Algebra Z O]
    [Algebra Z W] (f g f' g' : W →ₐ[Z] W) (h : ∀ w, f (g w) = f' (g' w)) (x : O ⊗[Z] W) :
    Algebra.TensorProduct.map (AlgHom.id O O) f (Algebra.TensorProduct.map (AlgHom.id O O) g x) =
    Algebra.TensorProduct.map (AlgHom.id O O) f' (Algebra.TensorProduct.map (AlgHom.id O O) g' x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a w => simp [h]

theorem map_id_comp {Z O W : Type} [CommRing Z] [CommRing O] [CommRing W] [Algebra Z O]
    [Algebra Z W] (f f' g' : W →ₐ[Z] W) (h : ∀ w, f w = f' (g' w)) (x : O ⊗[Z] W) :
    Algebra.TensorProduct.map (AlgHom.id O O) f x =
    Algebra.TensorProduct.map (AlgHom.id O O) f' (Algebra.TensorProduct.map (AlgHom.id O O) g' x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a w => simp [h]

theorem map_id_id {Z O W : Type} [CommRing Z] [CommRing O] [CommRing W] [Algebra Z O]
    [Algebra Z W] (f : W →ₐ[Z] W) (h : ∀ w, f w = w) (x : O ⊗[Z] W) :
    Algebra.TensorProduct.map (AlgHom.id O O) f x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a w => simp [h]

section Concrete

variable {l : ℕ} [Fact l.Prime]

theorem gRW_one {P : LocPrime l} (AI : LocAinf l P) (LL : FinExt l) (x : RW LL) : AI.gRW LL 1 x = x :=
  map_id_id _ (fun w => by simp) x

theorem gRW_mul {P : LocPrime l} (AI : LocAinf l P) (LL : FinExt l) (g h : GQ l) (x : RW LL) :
    AI.gRW LL (g * h) x = AI.gRW LL g (AI.gRW LL h x) :=
  map_id_comp _ _ _ (fun w => by simp) x

theorem phi_gRW {P : LocPrime l} (AI : LocAinf l P) (LL : FinExt l) (g : GQ l) (x : RW LL) :
    φRW LL (AI.gRW LL g x) = AI.gRW LL g (φRW LL x) := by
  refine map_id_comm _ _ _ _ (fun w => ?_) x
  ext n
  change frobenius (Cb l) l (autCb l (AI.actT g) (w.coeff n)) =
    autCb l (AI.actT g) (frobenius (Cb l) l (w.coeff n))
  simp [frobenius_def]

theorem compact_GK (K : FinExt l) : CompactSpace ↥(GK K) :=
  isCompact_iff_compactSpace.1 (InfiniteGalois.fixingSubgroup_isClosed K.1).isCompact

end Concrete

theorem exists_classMaps : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ)
    (LL : FinExt l), Good K s LL → ∀ (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R), IoW I →
    ∀ E : WEt I, Nonempty (WCl E) := by
  intro l _ P AI K s LL hg Γ R I _ E
  have := compact_GK K
  have hT : ∀ T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL),
      Setup (φRW LL) (fun g : ↥(GK K) => AI.gRW LL (g : GQ l)) l T := fun T =>
    ⟨⟨(GlobalTheory.T.frobenius_sub_one_wittTensorLattice_surjective_fixed l K LL T).1, fun b => ((GlobalTheory.T.frobenius_sub_one_wittTensorLattice_surjective_fixed l K LL T).2.1 b).1⟩, GlobalTheory.T.exists_weak_topology_witt_tilt_tensor l P AI K LL T⟩
  exact nonempty_cl (l := l) (I := I) (gRW_one AI LL) (fun g h => gRW_mul AI LL (g : GQ l) (h : GQ l))
    (fun g => phi_gRW AI LL (g : GQ l)) hT (GlobalTheory.T.exists_gammaLayer_padic_coordinates l P K s LL hg Γ) E

end GlobalTheory.HerrClassMaps
