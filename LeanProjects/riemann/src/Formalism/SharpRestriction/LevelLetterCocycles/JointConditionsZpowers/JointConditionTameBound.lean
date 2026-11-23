import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineMapLemmas
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.BaseFont

noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Module

section Ker

variable {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL] [Algebra Qp LL]
    [TopologicalSpace LL] [IsTopologicalRing LL] [CommRing O] [Algebra O LL]

def LocLat.ofGRep (A : GRep G Qp LL O) (L : Lattice (O := O) A.ρ) : LocLat G Qp LL O :=
  { V := A.V, ρ := A.ρ, cont := A.cont, L := L }

variable (Yt : LocLat G Qp LL O) (p : Yt.V →ₗ[LL] LL) (e₀ : Yt.V) (hpe : p e₀ = 1)

theorem ker_stable (hp : ∀ g v, p (Yt.ρ g v) = p v) :
    ∀ g, ∀ u ∈ LinearMap.ker p, Yt.ρ g u ∈ LinearMap.ker p := by
  intro g u hu
  rw [LinearMap.mem_ker] at hu ⊢
  exact (hp g u).trans hu

def kerProj : Yt.V →ₗ[LL] ↥(LinearMap.ker p) :=
  LinearMap.codRestrict _ (LinearMap.id - (LinearMap.toSpanSingleton LL Yt.V e₀) ∘ₗ p) (by
    intro v
    rw [LinearMap.mem_ker]
    simp [hpe])

theorem kerProj_coe (v : Yt.V) : ((kerProj Yt p e₀ hpe v : ↥(LinearMap.ker p)) : Yt.V) = v - p v • e₀ := rfl

theorem kerProj_of_mem (u : ↥(LinearMap.ker p)) : kerProj Yt p e₀ hpe (u : Yt.V) = u := by
  apply Subtype.ext
  rw [kerProj_coe, LinearMap.mem_ker.mp u.2, zero_smul, sub_zero]

def kerT : Submodule O ↥(LinearMap.ker p) :=
  Yt.L.T.comap ((LinearMap.ker p).subtype.restrictScalars O)

theorem kerT_eq_map (hint : ∀ v ∈ Yt.L.T, p v ∈ Set.range (algebraMap O LL)) (he₀ : e₀ ∈ Yt.L.T) :
    kerT Yt p = Yt.L.T.map ((kerProj Yt p e₀ hpe).restrictScalars O) := by
  ext u
  constructor
  · intro hu
    exact ⟨(u : Yt.V), hu, kerProj_of_mem Yt p e₀ hpe u⟩
  · rintro ⟨v, hv, rfl⟩
    show ((kerProj Yt p e₀ hpe v : ↥(LinearMap.ker p)) : Yt.V) ∈ Yt.L.T
    rw [kerProj_coe]
    obtain ⟨a, ha⟩ := hint v hv
    rw [← ha, algebraMap_smul]
    exact Yt.L.T.sub_mem hv (Yt.L.T.smul_mem a he₀)

theorem kerT_free [IsDomain O] [IsPrincipalIdealRing O] : Module.Free O ↥(kerT Yt p) := by
  have := Yt.L.free
  have : Module.Finite O ↥Yt.L.T := Module.Finite.iff_fg.mpr Yt.L.fg
  let N' : Submodule O ↥Yt.L.T := LinearMap.ker ((p.restrictScalars O) ∘ₗ Yt.L.T.subtype)
  obtain ⟨n, ⟨b⟩⟩ := Submodule.nonempty_basis_of_pid (Module.Free.chooseBasis O ↥Yt.L.T) N'
  have hN : Module.Free O ↥N' := Module.Free.of_basis b
  let eqv : ↥N' ≃ₗ[O] ↥(kerT Yt p) :=
    { toFun := fun t => ⟨⟨(t : ↥Yt.L.T), t.2⟩, (t : ↥Yt.L.T).2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun u => ⟨⟨((u : ↥(LinearMap.ker p)) : Yt.V), u.2⟩, (u : ↥(LinearMap.ker p)).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact Module.Free.of_equiv eqv

include hpe in
theorem kerT_span (hint : ∀ v ∈ Yt.L.T, p v ∈ Set.range (algebraMap O LL)) (he₀ : e₀ ∈ Yt.L.T) :
    Submodule.span LL ((kerT Yt p : Submodule O ↥(LinearMap.ker p)) : Set ↥(LinearMap.ker p)) = ⊤ := by
  rw [eq_top_iff]
  intro u _
  have h1 : (u : Yt.V) ∈ Submodule.span LL (Yt.L.T : Set Yt.V) := by
    rw [Yt.L.span]
    trivial
  have h2 := Submodule.mem_map_of_mem (f := kerProj Yt p e₀ hpe) h1
  rw [kerProj_of_mem, Submodule.map_span] at h2
  refine Submodule.span_mono ?_ h2
  rintro _ ⟨v, hv, rfl⟩
  rw [SetLike.mem_coe, kerT_eq_map Yt p e₀ hpe hint he₀]
  exact ⟨v, hv, rfl⟩

def kerLat [IsDomain O] [IsPrincipalIdealRing O] (hp : ∀ g v, p (Yt.ρ g v) = p v)
    (hint : ∀ v ∈ Yt.L.T, p v ∈ Set.range (algebraMap O LL)) (he₀ : e₀ ∈ Yt.L.T) :
    Lattice (O := O) (subRho (GRep.ofLat Yt) (LinearMap.ker p) (ker_stable Yt p hp)) where
  T := kerT Yt p
  stable := fun g x hx => Yt.L.stable g x hx
  fg := by
    rw [kerT_eq_map Yt p e₀ hpe hint he₀]
    exact Yt.L.fg.map _
  free := kerT_free Yt p
  span := kerT_span Yt p e₀ hpe hint he₀

def kerY [IsDomain O] [IsPrincipalIdealRing O] (hp : ∀ g v, p (Yt.ρ g v) = p v)
    (hint : ∀ v ∈ Yt.L.T, p v ∈ Set.range (algebraMap O LL)) (he₀ : e₀ ∈ Yt.L.T) : LocLat G Qp LL O :=
  LocLat.ofGRep ((GRep.ofLat Yt).sub (LinearMap.ker p) (ker_stable Yt p hp)) (kerLat Yt p e₀ hpe hp hint he₀)

variable (G Qp LL O) in

def trivZ (hinj : Function.Injective (algebraMap O LL)) : LocLat G Qp LL O :=
  { V := LL
    ρ := 1
    cont := fun _ => continuous_const
    L :=
      { T := LinearMap.range (Algebra.linearMap O LL)
        stable := fun _ _ hx => hx
        fg := by
          rw [LinearMap.range_eq_map]
          exact Submodule.FG.map _ Module.Finite.fg_top
        free := Module.Free.of_equiv (LinearEquiv.ofInjective (Algebra.linearMap O LL) hinj)
        span := by
          rw [eq_top_iff]
          intro x _
          have h1 : (1 : LL) ∈ Submodule.span LL ((LinearMap.range (Algebra.linearMap O LL) : Submodule O LL) : Set LL) :=
            Submodule.subset_span ⟨1, by simp⟩
          have := Submodule.smul_mem _ x h1
          simpa using this } }

end Ker

def JointConditionTameBound (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (π : D.nd.X i) (M0 h0 cB : ℕ) : Prop :=
  D.nd.l i ≠ 2 ∧ ∀ (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)),
    Br.inert D.nbr i w hw = IK (D.nbr i w hw).Kw ∧ (D.nbr i w hw).Kw.1 ≤ Ks (D.nbr i w hw).Kw 1 ∧
    ∀ (C : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hs : Good (D.nbr i w hw).Kw 1 C.LL)
      (Y : LocLat (Br.G D.nbr i w hw) ℚ_[D.nd.l i] ↥C.LL.1 ↥(OL C.LL)),
      IsCrys (Br.PD D.loc D.nbr i w hw) Y.ρ →
      (∀ τ, JumpsInV (Br.PD D.loc D.nbr i w hw) Y.ρ τ
        {a | IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r π))) τ a}) →
      (∀ a ∈ Formalism.MainNotions.LocalSituation.Jset (Formalism.MainNotions.LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 C.LL hs) Y,
        -(M0 : ℤ) ≤ a ∧ a ≤ h0) ∧
      ∀ e < D.R.t, Formalism.MainNotions.LocalSituation.cTBY
        (Formalism.MainNotions.LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 C.LL hs) Y M0 h0 e ≤ cB

end Formalism.MainNotions.N
