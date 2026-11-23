import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.MapEta
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.ResidDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.PairDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.ComapLam
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.MapStar

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa
open scoped TensorProduct

noncomputable section

private theorem gdet_comap_comap {n : ℕ} {A G G' G'' : Type} [CommRing A] [Group G] [Group G'] [Group G'']
    (D : GDet n A G'') (f : G →* G') (f' : G' →* G'') : (D.comap f').comap f = D.comap (f'.comp f) := by
  apply GDet.ext
  intro B _ _ x
  show (D.D B) ((MonoidAlgebra.mapDomainRingHom B f') ((MonoidAlgebra.mapDomainRingHom B f) x)) =
    (D.D B) (MonoidAlgebra.mapDomainRingHom B (f'.comp f) x)
  rw [MonoidAlgebra.mapDomainRingHom_comp, RingHom.comp_apply]

private theorem mapDom_single {A G G' : Type} [CommRing A] [Group G] [Group G'] (f : G →* G') (a : G) (c : A) :
    MonoidAlgebra.mapDomainRingHom A f (MonoidAlgebra.single a c) = MonoidAlgebra.single (f a) c := by
  simp

section

variable {l : ℕ} [Fact l.Prime] {L : Loc} {G0 G0' G G' : Glob l L} {n : ℕ} {O : Type} [CommRing O] [IsLocalRing O]
  [Algebra ℤ_[l] O] {r : Resid G0.frame O n} {r' : Resid G0'.frame O n} {B : Type} [CommRing B] [Algebra O B] [IsCO O B]
  {u : Pair r B} {u' : Pair r' B} {J : Ideal B} {σ : Type} {D : ℕ}

@[reducible] private def baseDesc (b : TWBase u J σ D) (hr : r.psib = r'.psib) (hψ : u'.ψ = u.ψ) : TWBase u' J σ D where
  wt := b.wt
  wt_res k := by rw [← hr]; exact b.wt_res k
  lam := b.lam
  segmentWeightExponent k := by rw [hψ]; exact b.segmentWeightExponent k
  M := b.M
  smul_lam := b.smul_lam
  free := b.free
  fin := b.fin
  supp := b.supp

variable {b : TWBase u J σ D} {h : G.Hom G0} {h' : G'.Hom G0'} {q : ℕ} {ut : Fin q → Fin n → O} {N : ℕ}

@[reducible] private def ringDesc (A : TWRing b h ut N) (hr : r.psib = r'.psib) (hψ : u'.ψ = u.ψ)
    (rN' : Resid G'.frame O n) (hc : Glob.Compat h' rN' r') (p' : Pair rN' A.R) (hp : p'.ψ = A.p.ψ) :
    TWRing (baseDesc b hr hψ) h' ut N where
  rN := rN'
  compat := hc
  R := A.R
  p := p'
  s := A.s
  s_w k := by rw [hp]; exact A.s_w k
  U := A.U
  U_res := A.U_res
  M := A.M
  a := A.a
  le_a := A.le_a
  rk := A.rk
  e := A.e
  e_smul := A.e_smul

private def MapsP (A : TWRing b h ut N) (Nq : Fin q → ℕ) (P : Fin q → Polynomial B) : Prop :=
  ∃ (θ : A.R →ₐ[O] Sp P fun j i => algebraMap O B (ut j i))
    (φ : (Sp P fun j i => algebraMap O B (ut j i)) ⊗[B] b.M →+ A.X)
    (ψ : A.X →+ (Sp P fun j i => algebraMap O B (ut j i)) ⊗[B] b.M),
    (A.p.Maps θ.toRingHom ((u.D.comap h.p₀).map (algebraMap B _)) fun v i => pushCh (algebraMap B _) (u.ψ v i)) ∧
    (∀ z, θ (A.s z) = algebraMap B _ (b.lam (MvPowerSeries.constantCoeff z))) ∧
    (∀ j i, θ (A.U j i) = Sp.u _ _ j i) ∧
    (∀ (t : A.R) z, φ (θ t • z) = t • φ z) ∧ (∀ (t : A.R) z, ψ (t • z) = θ t • ψ z) ∧
    (∀ z, φ (ψ z) = fEl Nq A.U • z) ∧ ∀ z, ψ (φ z) = θ (fEl Nq A.U) • z

private theorem maps_desc (A : TWRing b h ut N) (hr : r.psib = r'.psib) (hψ : u'.ψ = u.ψ)
    (rN' : Resid G'.frame O n) (hc : Glob.Compat h' rN' r') (p' : Pair rN' A.R) (hp : p'.ψ = A.p.ψ)
    (g0 : G0.Hom G0') (g : G.Hom G') (comm : ∀ a, h'.p₀ (g.p₀ a) = g0.p₀ (h.p₀ a))
    (hD : u'.D.comap g0.p₀ = u.D) (hpD : p'.D.comap g.p₀ = A.p.D)
    (Nq : Fin q → ℕ) (ph ta : Fin q → G.G₀) (ex : ℕ) (m : TWMaps Nq ph ta A ex) :
    Nonempty (TWMaps Nq (fun j => g.p₀ (ph j)) (fun j => g.p₀ (ta j)) (ringDesc A hr hψ rN' hc p' hp) ex) := by
  have H : MapsP A Nq fun j => u.D.chi (MonoidAlgebra.single (h.p₀ (ph j)) 1) :=
    ⟨m.θ, m.φ, m.ψ, m.θ_pair, m.theta_coefficientMap_eq, m.θ_U, m.φ_smul, m.ψ_smul, m.φψ, m.ψφ⟩
  have e : (fun j => u.D.chi (MonoidAlgebra.single (h.p₀ (ph j)) 1)) =
      fun j => u'.D.chi (MonoidAlgebra.single (h'.p₀ (g.p₀ (ph j))) 1) := funext fun j => by
    rw [← hD, (comap_lam n B _ _ g0.p₀ u'.D).1, mapDom_single, comm]
  rw [e] at H
  obtain ⟨θ, φ, ψ, ⟨h1, h1'⟩, h2, h3, h4, h5, h6, h7⟩ := H
  have htr : ∀ y, p'.D.tr (MonoidAlgebra.mapDomainRingHom A.R g.p₀ y) = A.p.D.tr y := fun y => by
    rw [← hpD, (comap_lam n A.R _ _ g.p₀ p'.D).2.2.1]
  obtain ⟨-, -, s1, s2⟩ := map_star l L G G' g n O A.R
  refine ⟨⟨θ, ⟨?_, fun v i => ?_⟩, h2, h3, φ, ψ, h4, h5, h6, h7, fun j a x => ?_, fun j i a x => ?_⟩⟩
  · refine ((comap_lam n _ _ _ g.p₀ _).2.2.2.2.2 g.p₀_surj).1 _ ?_
    have e1 := (comap_lam n _ _ _ g.p₀ p'.D).2.2.2.1 _ θ.toRingHom
    have e2 := (comap_lam n _ _ _ g.p₀ (u'.D.comap h'.p₀)).2.2.2.1 _
      (algebraMap B (SpAt u' (fun j => h'.p₀ (g.p₀ (ph j))) ut))
    have e3 : (u'.D.comap h'.p₀).comap g.p₀ = u.D.comap h.p₀ := by
      rw [← hD, gdet_comap_comap, gdet_comap_comap]
      exact congrArg _ (MonoidHom.ext comm)
    rw [hpD] at e1
    rw [e3] at e2
    exact e1.symm.trans (h1.trans e2)
  · have := h1' v i
    rw [← hp, ← hψ] at this
    exact this
  · obtain ⟨a, rfl⟩ := g.p₀_surj a
    have := m.rel1 j a x
    rw [← htr, map_mul, mapDom_single, s1] at this
    exact this
  · obtain ⟨a, rfl⟩ := g.p₀_surj a
    have := m.rel2 j i a x
    rw [← htr, map_mul, mapDom_single, s2] at this
    exact this

end

private theorem apply_mem_openNormalSubgroup_of_mem_PL_comap (l : ℕ) {Γ Γ' : Type} [Group Γ] [TopologicalSpace Γ] [Group Γ']
    [TopologicalSpace Γ'] (f : Γ →* Γ') (hf : Continuous f) (H : OpenNormalSubgroup Γ') (a : Γ)
    (ha : a ∈ PL l (Subgroup.comap f (H.toOpenSubgroup : Subgroup Γ'))) :
    f a ∈ (H.toOpenSubgroup : Subgroup Γ') := by
  let U : OpenNormalSubgroup Γ :=
    { toOpenSubgroup := ⟨(H.toOpenSubgroup : Subgroup Γ').comap f, H.isOpen'.preimage hf⟩
      isNormal' := Subgroup.Normal.comap H.isNormal' f }
  have hU : PL l (Subgroup.comap f (H.toOpenSubgroup : Subgroup Γ')) ≤ (U.toOpenSubgroup : Subgroup Γ) :=
    iInf_le_of_le U (iInf_le_of_le (fun k hk => ⟨0, by rw [pow_zero, pow_one]; exact hk⟩) le_rfl)
  exact hU ha

theorem UpperTheory.V.Pa.aut_desc :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Q : TWQuot T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (r' : Resid Q.G0'.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (u' : Pair r' B) (J : Ideal B) (σ : Type) (D : ℕ), Adapted T (r := r) → Glob.Compat Q.g0 r r' → u'.D.comap Q.g0.p₀ = u.D → u'.ψ = u.ψ → TWAut u J σ D T → Nonempty (TWAut u' J σ D Q.grp) := by
  intro l _ L G0 T Q n O _ _ _ _ _ r r' B _ _ _ u u' J σ D hAd hC hD hψ W
  have hr : r.psib = r'.psib := hC.2.1
  have key : ∀ N : ℕ, ∃ (rN' : Resid (Q.GN' N).frame O n) (_ : Glob.Compat (Q.h' N) rN' r')
      (p' : Pair rN' (W.A N).R) (_ : p'.ψ = (W.A N).p.ψ), p'.D.comap (Q.gN N).p₀ = (W.A N).p.D := by
    intro N
    have hchi : ∀ (a : (T.GN N).G₀) (i : Fin n), (W.A N).rN.chib i a = r.chib i ((T.h N).p₀ a) :=
      fun a i => by rw [(W.A N).compat.1 i]; rfl
    have hH : ∀ a : (T.GN N).G₀,
        (a : (T.GN N).Γ) ∈ Subgroup.comap (T.h N).p (T.H.toOpenSubgroup : Subgroup G0.Γ) →
        ∀ i, (W.A N).rN.chib i a = 1 := by
      intro a ha i
      rw [hchi]
      exact hAd.1 ((T.h N).p₀ a) ha i
    obtain ⟨rN', hc1, _⟩ := resid_desc l L (T.GN N) (Q.GN' N) (Q.gN N) n O (W.A N).rN (by
      intro a ha i
      apply hH a _ i
      have hk : (a : (T.GN N).Γ) ∈ (Q.gN N).p.ker := by
        rw [MonoidHom.mem_ker]
        exact congrArg Subtype.val ha
      rw [Q.kerN N] at hk
      exact apply_mem_openNormalSubgroup_of_mem_PL_comap l (T.h N).p (T.h N).cont T.H _ hk)
    have hleη : Subgroup.comap (T.h N).p (T.H.toOpenSubgroup : Subgroup G0.Γ) ≤ (T.GN N).η.ker := by
      intro a ha
      rw [MonoidHom.mem_ker, ← (T.h N).η a]
      exact T.H_η _ ha
    obtain ⟨p', hpD, hp⟩ := pair_desc l L (T.GN N) (Q.GN' N) (Q.gN N) n O (W.A N).rN rN' (W.A N).R (W.A N).p
      (Subgroup.comap (T.h N).p (T.H.toOpenSubgroup : Subgroup G0.Γ))
      (T.H.isOpen'.preimage (T.h N).cont) hleη hH (Q.kerN N) hc1
    refine ⟨rN', ⟨fun i => ?_, ?_, ?_⟩, p', hp, hpD⟩
    · refine MonoidHom.ext fun b => ?_
      obtain ⟨a, rfl⟩ := (Q.gN N).p₀_surj b
      show rN'.chib i ((Q.gN N).p₀ a) = r'.chib i ((Q.h' N).p₀ ((Q.gN N).p₀ a))
      rw [Q.comm₀ N a]
      have e1 : (W.A N).rN.chib i a = rN'.chib i ((Q.gN N).p₀ a) := by rw [hc1.1 i]; rfl
      have e2 : r.chib i ((T.h N).p₀ a) = r'.chib i (Q.g0.p₀ ((T.h N).p₀ a)) := by rw [hC.1 i]; rfl
      rw [← e1, hchi, e2]
    · exact hc1.2.1.symm.trans ((W.A N).compat.2.1.trans hr)
    · exact hc1.2.2.symm.trans ((W.A N).compat.2.2.trans hC.2.2)
  choose rN' hc p' hp hpD using key
  refine ⟨⟨baseDesc W.b hr hψ, W.ut, ?_, fun N => ringDesc (W.A N) hr hψ (rN' N) (hc N) (p' N) (hp N),
    W.ex, fun N => ?_⟩⟩
  · intro j i
    rw [W.ut_res j i, hC.1 i]
    rfl
  · exact (maps_desc (W.A N) hr hψ (rN' N) (hc N) (p' N) (hp N) Q.g0 (Q.gN N) (Q.comm₀ N) hD (hpD N)
      (T.Nq N) (T.ph N) (T.ta N) W.ex (W.m N)).some
