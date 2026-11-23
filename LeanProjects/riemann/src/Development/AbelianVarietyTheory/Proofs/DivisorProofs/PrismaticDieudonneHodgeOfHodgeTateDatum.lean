import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FontaineAinfLocalDomainXiAdicOrder
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.MemSmulOfTmulEqZero
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.SemilinearFactorsThroughReduction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfHodgeTateLatticeConstQpModZpEquivStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueMuPInfinityHodgeTateLatticeMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivisibleGroupLatticeFreeRankHeightStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHodgeSequenceFirstMapLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupHodgeTateFirstMapNaturalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateSeparatesDualLieGhostComponentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateLatticeMuPInfinityFreeRankOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrobeniusHodgeTateLatticeAinfStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.PDivLat

set_option maxHeartbeats 2000000 in

theorem prismaticDieudonneHodgeAt_of_hasDatum : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), (∀ G : PDivGroup p O, HasDatum hε G) → GlobalTheory.Published.PrismaticDieudonneHodgeAt ε := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε hD
  have hε1 : IsPrimitiveRoot (root ε).untilt p := by simpa [zeta] using hε 1
  obtain ⟨hdom, -, hker, hθ, -, -, -⟩ := GlobalTheory.AinfXi.ainf_local_xi_order p C v O hv ε hε1
  haveI := hdom
  have hθξ : WittVector.fontaineTheta O p (xi ε) = 0 := by
    rw [← RingHom.mem_ker, hker]; exact Ideal.mem_span_singleton_self _
  have hμ : Sandwich.mu ε ≠ 0 := fun h => GlobalTheory.Dieudonne.not_dvd_mu hε1 (h ▸ dvd_zero _)

  obtain ⟨φ, hφ1, hφ2⟩ := GlobalTheory.T.exists_frobenius_hodgeTateLattice_ainf p C v O hv ε hε

  have hsep : ∀ (G : PDivGroup p O) (x x' : G.dual.Lie),
      (∀ t, x (hodgeTate G t) = x' (hodgeTate G t)) → x = x' := fun G x x' h =>
    sub_eq_zero.1 ((GlobalTheory.T.hodgeTate_separates_dual_lie_ghostComponent p C v O hv ε hε G (hD G)).1 (x - x') fun t => by
      rw [LinearMap.sub_apply, h, sub_self])
  have hqex : ∀ G : PDivGroup p O, ∃ q : latt G →ₛₗ[WittVector.fontaineTheta O p] G.dual.Lie,
      ∀ y t, q y (hodgeTate G t) = WittVector.fontaineTheta O p (y.1 t) := fun G => by
    choose x hx using fun y : latt G => y.2 0
    refine ⟨{ toFun := x
              map_add' := fun a b => hsep G _ _ (fun t => ?_)
              map_smul' := fun c a => hsep G _ _ (fun t => ?_) }, fun y t => (hx y t).symm⟩
    · rw [LinearMap.add_apply, ← hx, ← hx, ← hx]; exact ghost_add 0 (a.1 t) (b.1 t)
    · rw [LinearMap.smul_apply, ← hx, ← hx, smul_eq_mul]; exact ghost_mul 0 c (a.1 t)
  choose q hq using hqex

  haveI hadd : (lattFunctor p O).Additive :=
    { map_add := fun {X Y f g} => ModuleCat.hom_ext (LinearMap.ext fun y =>
        Subtype.ext (LinearMap.ext fun t => by
          change y.1 (tateMap _ _ O (f + g).unop t) =
            y.1 (tateMap _ _ O f.unop t) + y.1 (tateMap _ _ O g.unop t)
          rw [unop_add, map_add, LinearMap.add_apply, map_add])) }

  obtain ⟨D, r, hr, nr⟩ := GlobalTheory.CompanionTheory.ModuleReduction.exists_reduction (Ainf p O) O
    (WittVector.fontaineTheta O p) hθ (xi ε) hker (PDivGroup p O)ᵒᵖ (lattFunctor p O)

  have hπex : ∀ G : PDivGroup p O, ∃ π : D.obj (op G) →ₗ[O] G.dual.Lie,
      ∀ m, π (r (op G) m) = q G m := fun G =>
    GlobalTheory.CompanionTheory.Div.semilinear_factors_through_reduction (Ainf p O) O (WittVector.fontaineTheta O p) hθ
      (xi ε) hθξ _ (D.obj (op G)) G.dual.Lie (r (op G)) (q G) (hr (op G)).1 (hr (op G)).2
  choose π hπ using hπex

  have hιex := fun G : PDivGroup p O => GlobalTheory.T.exists_hodgeSequence_first_map_lattice p C v O hv ε hε G (hD G) (D.obj (op G))
    (r (op G)) (π G) (hr (op G)).1 (hr (op G)).2 (fun y t => (LinearMap.congr_fun (hπ G y) _).trans (hq G y t))
  choose ι hι using hιex
  have nr' : ∀ (G H : PDivGroup p O) (f : G ⟶ H) (m : latt H),
      (D.map f.op).hom (r (op H) m) = r (op G) (lattMap f m) := fun G H f m => nr _ _ f.op m
  refine ⟨lattFunctor p O, D, φ, fun G => r (op G), ι, π, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hadd
  · exact fun G => GlobalTheory.T.pDivisibleGroup_lattice_free_rank_height p C v O hv ε hε G (hD G)
  · intro G m
    obtain ⟨n, hn⟩ := hφ2 G m
    exact ⟨n, hn⟩
  · intro G H f m
    refine Subtype.ext (LinearMap.ext fun t => ?_)
    exact (hφ1 H m _).trans (hφ1 G (lattMap f m) t).symm
  · exact fun G => hr (op G)
  · exact fun G H f m => nr' G H f m
  · intro G
    refine ⟨(hι G).1, (hι G).2.1, fun x => ?_⟩
    obtain ⟨y, hy⟩ := (GlobalTheory.T.hodgeTate_separates_dual_lie_ghostComponent p C v O hv ε hε G (hD G)).2 x
    exact ⟨r (op G) y, (hπ G y).trans (hsep G _ _ fun t => (hq G y t).trans (hy t))⟩
  · intro G H f w
    exact GlobalTheory.T.pDivGroup_hodgeTateFirstMap_natural p C v O hv ε hε G H f (hD G) (hD H) (D.obj (op G)) (r (op G)) (D.obj (op H))
      (r (op H)) (D.map f.op).hom (ι G) (ι H) (hr (op G)).1 (hr (op G)).2 (nr' G H f)
      (hι G).2.2 (hι H).2.2 w
  · intro G H f x
    obtain ⟨m, rfl⟩ := (hr (op H)).1 x
    refine ((congrArg (π G) (nr' G H f m)).trans (hπ G _)).trans ?_
    refine (hsep G _ _ fun t => ?_).trans (congrArg _ (hπ H m).symm)
    exact (hq G _ t).trans ((hq H m _).symm.trans (congrArg (q H m) (hodgeTate_tateMap f t)))
  · obtain ⟨e, he⟩ := GlobalTheory.T.ainfHodgeTateLattice_constQpModZp_equiv p C v O hv ε hε
    exact ⟨e, fun m => (he _).trans ((hφ1 _ _ _).trans (congrArg _ (he m).symm))⟩
  · obtain ⟨e, he⟩ := GlobalTheory.T.hodgeTateLattice_muPInfinity_free_rank_one p C v O hv ε hε
    refine ⟨e, fun m => mul_left_cancel₀ hμ ?_⟩
    have h1 : Sandwich.mu ε * e (φ _ m) = WittVector.frobenius (Sandwich.mu ε * e m) :=
      (he _).trans ((hφ1 _ _ _).trans (congrArg _ (he m).symm))
    have h2 : WittVector.frobenius (Sandwich.mu ε * e m) =
        Sandwich.mu ε * (WittVector.frobenius (xi ε) * WittVector.frobenius (e m)) := by
      rw [map_mul, GlobalTheory.Dieudonne.frobenius_mu]
      ring
    exact h1.trans h2
  · intro g hg
    obtain ⟨f, hf, hu⟩ := GlobalTheory.T.existsUnique_muPInfinity_hodgeTate_lattice_map p C v O hv ε hε g fun m m' hm t => by
      have e : m' = φ _ m := Subtype.ext (LinearMap.ext fun t => by rw [hm, hφ1])
      subst e
      exact (congrArg (fun z => z.1 t) (hg m)).trans (hφ1 _ _ t)
    exact ⟨f, hf, fun f' hf' => hu f' hf'⟩

end GlobalTheory.PDivLat
