import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.QuotStage

noncomputable section

open MeasureTheory Topology Filter UpperTheory.ConvolutionTheory.G
open scoped ENNReal Pointwise

namespace UpperTheory.ConvolutionTheory.T4

section
variable {V G Gi : Type} {Gv : V → Type} [Group G] [Group Gi] [∀ v, Group (Gv v)]

def US (p : ∀ v, G →* Gv v) (K : ∀ v, Subgroup (Gv v)) (S : Finset V) : Subgroup G where
  carrier := {g | ∀ v ∉ S, p v g ∈ K v}
  one_mem' v _ := by rw [map_one]; exact one_mem _
  mul_mem' {a b} ha hb v hv := by rw [map_mul]; exact mul_mem (ha v hv) (hb v hv)
  inv_mem' {a} ha v hv := by rw [map_inv]; exact inv_mem (ha v hv)

theorem mem_US {p : ∀ v, G →* Gv v} {K : ∀ v, Subgroup (Gv v)} {S : Finset V} {g : G} :
    g ∈ US p K S ↔ ∀ v ∉ S, p v g ∈ K v := Iff.rfl

def prS (q : G →* Gi) (p : ∀ v, G →* Gv v) (S : Finset V) : G →* Gi × ∀ v : S, Gv v :=
  q.prod (Pi.monoidHom fun v : S => p v)

theorem prS_apply (q : G →* Gi) (p : ∀ v, G →* Gv v) (S : Finset V) (g : G) :
    prS q p S g = (q g, fun v : S => p v g) := rfl

structure RP [TopologicalSpace G] [TopologicalSpace Gi] [∀ v, TopologicalSpace (Gv v)]
    (q : G →* Gi) (p : ∀ v, G →* Gv v) (K : ∀ v, Subgroup (Gv v)) : Prop where
  cq : Continuous q
  cp : ∀ v, Continuous (p v)
  opn : ∀ v, IsOpen (K v : Set (Gv v))
  cpt : ∀ v, IsCompact (K v : Set (Gv v))
  ae : ∀ g, ∀ᶠ v in cofinite, p v g ∈ K v
  opnU : ∀ S : Finset V, IsOpen (US p K S : Set G)
  ext : ∀ g g', q g = q g' → (∀ v, p v g = p v g') → g = g'
  surj : ∀ (gi : Gi) (gv : ∀ v, Gv v), (∀ᶠ v in cofinite, gv v ∈ K v) → ∃ g, q g = gi ∧ ∀ v, p v g = gv v
  prop : ∀ (Ci : Set Gi) (C : ∀ v, Set (Gv v)), IsCompact Ci → (∀ v, IsCompact (C v)) →
    (∀ᶠ v in cofinite, C v ⊆ K v) → IsCompact {g | q g ∈ Ci ∧ ∀ v, p v g ∈ C v}

def Eul [MeasurableSpace G] [MeasurableSpace Gi] [∀ v, MeasurableSpace (Gv v)]
    (q : G →* Gi) (p : ∀ v, G →* Gv v) (K : ∀ v, Subgroup (Gv v)) (μ : Measure G) (μi : Measure Gi)
    (m : ∀ v, Measure (Gv v)) (a : NNReal) (S : Finset V) : Prop :=
  (μ.restrict (US p K S : Set G)).map (prS q p S) = a • μi.prod (Measure.pi fun v : S => m v)

def cen (f : G →* Gi) (g : G) : Subgroup.centralizer {g} →* Subgroup.centralizer {f g} where
  toFun t := ⟨f t, by
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.1 t.2]⟩
  map_one' := Subtype.ext (map_one f)
  map_mul' s t := Subtype.ext (map_mul f _ _)

@[simp] theorem coe_cen (f : G →* Gi) (g : G) (t : Subgroup.centralizer {g}) : (cen f g t : Gi) = f t := rfl

end

def QPush : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (T : Type) [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T] [T2Space T]
    [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T]
    (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] (T' : Type) [Group T'] [TopologicalSpace T'] [IsTopologicalGroup T'] [LocallyCompactSpace T'] [T2Space T']
    [SecondCountableTopology T'] [MeasurableSpace T'] [BorelSpace T']
    (μ : Measure G) (j : T →* G) (ν : Measure T) (μ' : Measure H) (j' : T' →* H) (ν' : Measure T'), Pair μ j ν → Pair μ' j' ν' →
    ∀ U : Subgroup G, IsOpen (U : Set G) → ∀ (π : G →* H) (πT : T →* T'), Continuous π → Continuous πT →
    (∀ t, π (j t) = j' (πT t)) → (μ.restrict (U : Set G)).map π = μ' → (ν.restrict (j ⁻¹' (U : Set G))).map πT = ν' →
    ∀ (F : G → ℂ) (F' : H → ℂ), Measurable F → (∀ t g, F (j t * g) = F g) → Measurable F' → (∀ t g, F' (j' t * g) = F' g) →
      (∀ g, F g ≠ 0 → g ∈ Set.range j * (U : Set G)) → (∀ u ∈ U, F u = F' (π u)) → qI μ j ν F = qI μ' j' ν' F'

def SplitEquiv : Prop :=
  ∀ (G₁ R G : Type) [Group G₁] [TopologicalSpace G₁] [Group R] [TopologicalSpace R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (i : G₁ →* G) (d : G →* R) (c : R →* G), IsEmbedding i → Continuous d → Continuous c → (∀ s, d (c s) = s) →
    (∀ s g, c s * g = g * c s) → (∀ g, d g = 1 ↔ g ∈ Set.range i) →
    ∃ e : G₁ × R ≃ₜ* G, ∀ x, e x = i x.1 * c x.2

def SplitQ : Prop :=
  ∀ (G₁ : Type) [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [T2Space G₁]
    [SecondCountableTopology G₁] [MeasurableSpace G₁] [BorelSpace G₁] (T₁ : Type) [Group T₁] [TopologicalSpace T₁] [IsTopologicalGroup T₁] [LocallyCompactSpace T₁] [T2Space T₁]
    [SecondCountableTopology T₁] [MeasurableSpace T₁] [BorelSpace T₁]
    (R : Type) [Group R] [TopologicalSpace R] [IsTopologicalGroup R] [LocallyCompactSpace R] [T2Space R]
    [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (T : Type) [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T] [T2Space T]
    [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T]
    (μ : Measure G₁) (j₁ : T₁ →* G₁) (ν : Measure T₁) (l : Measure R), Pair μ j₁ ν → Uni l →
    ∀ (e : G₁ × R ≃ₜ* G) (eT : T₁ × R ≃ₜ* T) (j : T →* G), (∀ x, j (eT x) = e (j₁ x.1, x.2)) →
      Pair ((μ.prod l).map e) j ((ν.prod l).map eT) ∧ ∀ F : G → ℂ, Measurable F → (∀ t g, F (j t * g) = F g) →
        qI μ j₁ ν (fun x => F (e (x, 1))) = qI ((μ.prod l).map e) j ((ν.prod l).map eT) F

def UniOf : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure →
    (μ.IsMulRightInvariant → Uni μ) ∧ ((∀ s t : G, s * t = t * s) → Uni μ)

def HaarEx : Prop :=
  ∀ (V : Type) (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Gi : Type) [Group Gi] [TopologicalSpace Gi] [IsTopologicalGroup Gi] [LocallyCompactSpace Gi] [T2Space Gi]
    [SecondCountableTopology Gi] [MeasurableSpace Gi] [BorelSpace Gi]
    (Gv : V → Type) [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)] [∀ v, IsTopologicalGroup (Gv v)]
    [∀ v, LocallyCompactSpace (Gv v)] [∀ v, T2Space (Gv v)] [∀ v, SecondCountableTopology (Gv v)] [∀ v, MeasurableSpace (Gv v)]
    [∀ v, BorelSpace (Gv v)]
    (q : G →* Gi) (p : ∀ v, G →* Gv v) (K : ∀ v, Subgroup (Gv v)), RP q p K →
    ∀ (μ : Measure G) (μi : Measure Gi) (m : ∀ v, Measure (Gv v)), μ.IsHaarMeasure → μi.IsHaarMeasure → (∀ v, (m v).IsHaarMeasure) →
    ∀ S : Finset V, ∃ a : NNReal, a ≠ 0 ∧ Eul q p K μ μi m a S

def HaarConst : Prop :=
  ∀ (V : Type) (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Gi : Type) [Group Gi] [TopologicalSpace Gi] [IsTopologicalGroup Gi] [LocallyCompactSpace Gi] [T2Space Gi]
    [SecondCountableTopology Gi] [MeasurableSpace Gi] [BorelSpace Gi]
    (Gv : V → Type) [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)] [∀ v, IsTopologicalGroup (Gv v)]
    [∀ v, LocallyCompactSpace (Gv v)] [∀ v, T2Space (Gv v)] [∀ v, SecondCountableTopology (Gv v)] [∀ v, MeasurableSpace (Gv v)]
    [∀ v, BorelSpace (Gv v)]
    (q : G →* Gi) (p : ∀ v, G →* Gv v) (K : ∀ v, Subgroup (Gv v)), RP q p K →
    ∀ (μ : Measure G) (μi : Measure Gi) (m : ∀ v, Measure (Gv v)), μ.IsHaarMeasure → μi.IsHaarMeasure →
    (∀ v, (m v).IsHaarMeasure ∧ m v (K v) = 1) → ∃ a : NNReal, a ≠ 0 ∧ ∀ S : Finset V, Eul q p K μ μi m a S

def UniLoc : Prop :=
  ∀ (V : Type) (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Gi : Type) [Group Gi] [TopologicalSpace Gi] [IsTopologicalGroup Gi] [LocallyCompactSpace Gi] [T2Space Gi]
    [SecondCountableTopology Gi] [MeasurableSpace Gi] [BorelSpace Gi]
    (Gv : V → Type) [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)] [∀ v, IsTopologicalGroup (Gv v)]
    [∀ v, LocallyCompactSpace (Gv v)] [∀ v, T2Space (Gv v)] [∀ v, SecondCountableTopology (Gv v)] [∀ v, MeasurableSpace (Gv v)]
    [∀ v, BorelSpace (Gv v)]
    (q : G →* Gi) (p : ∀ v, G →* Gv v) (K : ∀ v, Subgroup (Gv v)), RP q p K →
    ∀ (μ : Measure G) (μi : Measure Gi) (m : ∀ v, Measure (Gv v)), Uni μ → μi.IsHaarMeasure → (∀ v, (m v).IsHaarMeasure) →
    Uni μi ∧ ∀ v, Uni (m v)

def RPCen : Prop :=
  ∀ (V G Gi : Type) (Gv : V → Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [Group Gi] [TopologicalSpace Gi] [IsTopologicalGroup Gi] [T2Space Gi]
    [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)] [∀ v, IsTopologicalGroup (Gv v)] [∀ v, T2Space (Gv v)]
    (q : G →* Gi) (p : ∀ v, G →* Gv v) (K : ∀ v, Subgroup (Gv v)), RP q p K → ∀ g : G,
    RP (cen q g) (fun v => cen (p v) g) (fun v => (K v).comap (Subgroup.centralizer {p v g}).subtype)

def EulerSupp : Prop :=
  ∀ (V : Type) (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Gi : Type) [Group Gi] [TopologicalSpace Gi] [IsTopologicalGroup Gi] [LocallyCompactSpace Gi] [T2Space Gi]
    [SecondCountableTopology Gi] [MeasurableSpace Gi] [BorelSpace Gi]
    (Gv : V → Type) [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)] [∀ v, IsTopologicalGroup (Gv v)]
    [∀ v, LocallyCompactSpace (Gv v)] [∀ v, T2Space (Gv v)] [∀ v, SecondCountableTopology (Gv v)] [∀ v, MeasurableSpace (Gv v)]
    [∀ v, BorelSpace (Gv v)]
    (q : G →* Gi) (p : ∀ v, G →* Gv v) (K : ∀ v, Subgroup (Gv v))
    (T : Type) [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T] [T2Space T]
    [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T] (Ti : Type) [Group Ti] [TopologicalSpace Ti] [IsTopologicalGroup Ti] [LocallyCompactSpace Ti] [T2Space Ti]
    [SecondCountableTopology Ti] [MeasurableSpace Ti] [BorelSpace Ti]
    (Tv : V → Type) [∀ v, Group (Tv v)] [∀ v, TopologicalSpace (Tv v)] [∀ v, IsTopologicalGroup (Tv v)]
    [∀ v, LocallyCompactSpace (Tv v)] [∀ v, T2Space (Tv v)] [∀ v, SecondCountableTopology (Tv v)] [∀ v, MeasurableSpace (Tv v)]
    [∀ v, BorelSpace (Tv v)]
    (qT : T →* Ti) (pT : ∀ v, T →* Tv v) (KT : ∀ v, Subgroup (Tv v)), RP q p K → RP qT pT KT →
    ∀ (j : T →* G) (ji : Ti →* Gi) (jv : ∀ v, Tv v →* Gv v), (∀ t, q (j t) = ji (qT t)) → (∀ v t, p v (j t) = jv v (pT v t)) →
    (∀ v t, t ∈ KT v ↔ jv v t ∈ K v) →
    ∀ S : Finset V, ∀ (Fi : Gi → ℂ) (Fv : ∀ v, Gv v → ℂ), Measurable Fi → (∀ t g, Fi (ji t * g) = Fi g) →
    (∀ v, Measurable (Fv v) ∧ ∀ t g, Fv v (jv v t * g) = Fv v g) →
    (∀ v ∉ S, ∀ x, ((∃ t, ∃ y ∈ K v, x = jv v t * y) → Fv v x = 1) ∧ ((¬ ∃ t, ∃ y ∈ K v, x = jv v t * y) → Fv v x = 0)) →
    Measurable (fun g => Fi (q g) * ∏ᶠ v, Fv v (p v g)) ∧
    (∀ g, Fi (q g) * ∏ᶠ v, Fv v (p v g) ≠ 0 → g ∈ Set.range j * (US p K S : Set G)) ∧
    ∀ u ∈ US p K S, Fi (q u) * ∏ᶠ v, Fv v (p v u) = Fi (q u) * ∏ v : S, Fv v (p v u)

def Euler : Prop :=
  ∀ (V : Type) (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Gi : Type) [Group Gi] [TopologicalSpace Gi] [IsTopologicalGroup Gi] [LocallyCompactSpace Gi] [T2Space Gi]
    [SecondCountableTopology Gi] [MeasurableSpace Gi] [BorelSpace Gi]
    (Gv : V → Type) [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)] [∀ v, IsTopologicalGroup (Gv v)]
    [∀ v, LocallyCompactSpace (Gv v)] [∀ v, T2Space (Gv v)] [∀ v, SecondCountableTopology (Gv v)] [∀ v, MeasurableSpace (Gv v)]
    [∀ v, BorelSpace (Gv v)]
    (q : G →* Gi) (p : ∀ v, G →* Gv v) (K : ∀ v, Subgroup (Gv v))
    (T : Type) [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T] [T2Space T]
    [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T] (Ti : Type) [Group Ti] [TopologicalSpace Ti] [IsTopologicalGroup Ti] [LocallyCompactSpace Ti] [T2Space Ti]
    [SecondCountableTopology Ti] [MeasurableSpace Ti] [BorelSpace Ti]
    (Tv : V → Type) [∀ v, Group (Tv v)] [∀ v, TopologicalSpace (Tv v)] [∀ v, IsTopologicalGroup (Tv v)]
    [∀ v, LocallyCompactSpace (Tv v)] [∀ v, T2Space (Tv v)] [∀ v, SecondCountableTopology (Tv v)] [∀ v, MeasurableSpace (Tv v)]
    [∀ v, BorelSpace (Tv v)]
    (qT : T →* Ti) (pT : ∀ v, T →* Tv v) (KT : ∀ v, Subgroup (Tv v)), RP q p K → RP qT pT KT →
    ∀ (j : T →* G) (ji : Ti →* Gi) (jv : ∀ v, Tv v →* Gv v), (∀ t, q (j t) = ji (qT t)) → (∀ v t, p v (j t) = jv v (pT v t)) →
    (∀ v t, t ∈ KT v ↔ jv v t ∈ K v) →
    ∀ (μ : Measure G) (μi : Measure Gi) (m : ∀ v, Measure (Gv v)) (ν : Measure T) (νi : Measure Ti) (nv : ∀ v, Measure (Tv v)),
    Pair μ j ν → Pair μi ji νi → (∀ v, Pair (m v) (jv v) (nv v)) → ∀ (S : Finset V) (a b : NNReal), a ≠ 0 → b ≠ 0 →
    Eul q p K μ μi m a S → Eul qT pT KT ν νi nv b S →
    ∀ (Fi : Gi → ℂ) (Fv : ∀ v, Gv v → ℂ), Measurable Fi → (∀ t g, Fi (ji t * g) = Fi g) →
    (∀ v, Measurable (Fv v) ∧ ∀ t g, Fv v (jv v t * g) = Fv v g) →
    (∀ v ∉ S, ∀ x, ((∃ t, ∃ y ∈ K v, x = jv v t * y) → Fv v x = 1) ∧ ((¬ ∃ t, ∃ y ∈ K v, x = jv v t * y) → Fv v x = 0)) →
    Measurable (fun g => Fi (q g) * ∏ᶠ v, Fv v (p v g)) ∧
    qI μ j ν (fun g => Fi (q g) * ∏ᶠ v, Fv v (p v g)) =
      ((a : ℝ) : ℂ) / ((b : ℝ) : ℂ) * qI μi ji νi Fi * ∏ v ∈ S, qI (m v) (jv v) (nv v) (Fv v)

def Fub : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (T : Type) [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T] [T2Space T]
    [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T]
    (μ : Measure G) (j : T →* G) (ν : Measure T), Pair μ j ν → ∀ (θ : G →* G) (δ : G) (z : ℝ → G), Continuous θ → Continuous z →
    (∀ t, (j t)⁻¹ * δ * θ (j t) = δ) →
    (∀ D : Set G, IsCompact D → ∃ C : Set G, IsCompact C ∧ ∀ x, x⁻¹ * δ * θ x ∈ D → ∃ t, ∃ y ∈ C, x = j t * y) →
    (∀ D : Set G, IsCompact D → ∃ B : Set ℝ, IsCompact B ∧ ∀ s x, z s * (x⁻¹ * δ * θ x) ∈ D → s ∈ B) →
    ∀ φ : G → ℂ, Continuous φ → HasCompactSupport φ →
      Measurable (fun x => ∫ s, φ (z s * (x⁻¹ * δ * θ x))) ∧
      qI μ j ν (fun x => ∫ s, φ (z s * (x⁻¹ * δ * θ x))) = ∫ s, qI μ j ν (fun x => φ (z s * (x⁻¹ * δ * θ x)))

def SideAbs : Prop :=
  ∀ (V : Type) (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Gi : Type) [Group Gi] [TopologicalSpace Gi] [IsTopologicalGroup Gi] [LocallyCompactSpace Gi] [T2Space Gi]
    [SecondCountableTopology Gi] [MeasurableSpace Gi] [BorelSpace Gi]
    (Gv : V → Type) [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)] [∀ v, IsTopologicalGroup (Gv v)]
    [∀ v, LocallyCompactSpace (Gv v)] [∀ v, T2Space (Gv v)] [∀ v, SecondCountableTopology (Gv v)] [∀ v, MeasurableSpace (Gv v)]
    [∀ v, BorelSpace (Gv v)]
    (q : G →* Gi) (p : ∀ v, G →* Gv v) (K : ∀ v, Subgroup (Gv v))
    (T : Type) [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T] [T2Space T]
    [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T] (Ti : Type) [Group Ti] [TopologicalSpace Ti] [IsTopologicalGroup Ti] [LocallyCompactSpace Ti] [T2Space Ti]
    [SecondCountableTopology Ti] [MeasurableSpace Ti] [BorelSpace Ti]
    (Tv : V → Type) [∀ v, Group (Tv v)] [∀ v, TopologicalSpace (Tv v)] [∀ v, IsTopologicalGroup (Tv v)]
    [∀ v, LocallyCompactSpace (Tv v)] [∀ v, T2Space (Tv v)] [∀ v, SecondCountableTopology (Tv v)] [∀ v, MeasurableSpace (Tv v)]
    [∀ v, BorelSpace (Tv v)]
    (qT : T →* Ti) (pT : ∀ v, T →* Tv v) (KT : ∀ v, Subgroup (Tv v)), RP q p K → RP qT pT KT →
    ∀ (j : T →* G) (ji : Ti →* Gi) (jv : ∀ v, Tv v →* Gv v), (∀ t, q (j t) = ji (qT t)) → (∀ v t, p v (j t) = jv v (pT v t)) →
    (∀ v t, t ∈ KT v ↔ jv v t ∈ K v) →
    ∀ (μ : Measure G) (μi : Measure Gi) (m : ∀ v, Measure (Gv v)) (ν : Measure T) (νi : Measure Ti) (nv : ∀ v, Measure (Tv v)),
    Pair μ j ν → Pair μi ji νi → (∀ v, Pair (m v) (jv v) (nv v)) → ∀ (S : Finset V) (a b : NNReal), a ≠ 0 → b ≠ 0 →
    Eul q p K μ μi m a S → Eul qT pT KT ν νi nv b S →
    ∀ (θ : G →* G) (θi : Gi →* Gi) (θv : ∀ v, Gv v →* Gv v), (∀ g, q (θ g) = θi (q g)) → (∀ v g, p v (θ g) = θv v (p v g)) →
    Continuous θi → (∀ v, Continuous (θv v)) → ∀ (δ : G) (z : ℝ → G), Continuous z → (∀ v s, p v (z s) = 1) →
    (∀ t, (j t)⁻¹ * δ * θ (j t) = δ) →
    (∀ D : Set Gi, IsCompact D → ∃ C : Set Gi, IsCompact C ∧ ∀ x, x⁻¹ * q δ * θi x ∈ D → ∃ t, ∃ y ∈ C, x = ji t * y) →
    (∀ D : Set Gi, IsCompact D → ∃ B : Set ℝ, IsCompact B ∧ ∀ s x, q (z s) * (x⁻¹ * q δ * θi x) ∈ D → s ∈ B) →
    ∀ (φi : Gi → ℂ) (φ : ∀ v, Gv v → ℂ), Continuous φi → HasCompactSupport φi → (∀ v, Continuous (φ v)) →
    (∀ v ∉ S, φ v = (K v : Set (Gv v)).indicator 1 ∧
      ∀ x, x⁻¹ * p v δ * θv v x ∈ K v ↔ ∃ t, ∃ y ∈ K v, x = jv v t * y) →
    Measurable (fun x => ∫ s, φi (q (z s * (x⁻¹ * δ * θ x))) * ∏ᶠ v, φ v (p v (z s * (x⁻¹ * δ * θ x)))) ∧
    qI μ j ν (fun x => ∫ s, φi (q (z s * (x⁻¹ * δ * θ x))) * ∏ᶠ v, φ v (p v (z s * (x⁻¹ * δ * θ x)))) =
      ((a : ℝ) : ℂ) / ((b : ℝ) : ℂ) * (∫ s, qI μi ji νi fun x => φi (q (z s) * (x⁻¹ * q δ * θi x))) *
        ∏ v ∈ S, qI (m v) (jv v) (nv v) fun x => φ v (x⁻¹ * p v δ * θv v x)

def SepSc : Prop :=
  ∀ (R : Type) [CommRing R] (n : ℕ) (r : Rˣ) (M : Matrix (Fin n) (Fin n) R), M.charpoly.Separable → ((r : R) • M).charpoly.Separable

def CentComm : Prop :=
  ∀ (F R : Type) [Field F] [CharZero F] [CommRing R] (f : F →+* R) (n : ℕ) (γ : Matrix (Fin n) (Fin n) F), γ.charpoly.Separable →
    ∀ s t : Matrix (Fin n) (Fin n) R, s * γ.map f = γ.map f * s → t * γ.map f = γ.map f * t → s * t = t * s

end UpperTheory.ConvolutionTheory.T4
