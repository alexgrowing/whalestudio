import Mathlib

noncomputable def UpperTheory.Reformulated.B.CoboundaryOfGenerator.ContAction.{u_1, u_2, u_3} :
    {R : Type u_1} →
      [inst : CommRing R] →
        {G : Type u_2} →
          [inst_1 : Group G] →
            [TopologicalSpace G] →
              {M : Type u_3} →
                [inst_3 : AddCommGroup M] →
                  [inst_4 :
                      @_root_.Module R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                        (@AddCommGroup.toAddCommMonoid M inst_3)] →
                    [TopologicalSpace M] →
                      @Representation R G M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                          (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst_1))
                          (@AddCommGroup.toAddCommMonoid M inst_3) inst_4 →
                        Prop :=
    fun {R : Type u_1} [inst : CommRing R] {G : Type u_2} [inst_1 : Group G] [inst_2 : TopologicalSpace G] {M : Type u_3}
        [inst_3 : AddCommGroup M]
        [inst_4 :
          @_root_.Module R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
            (@AddCommGroup.toAddCommMonoid M inst_3)]
        [inst_5 : TopologicalSpace M]
        (rho :
          @Representation R G M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
            (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst_1)) (@AddCommGroup.toAddCommMonoid M inst_3) inst_4) ↦
      @Continuous (Prod G M) M (@instTopologicalSpaceProd G M inst_2 inst_5) inst_5 fun (p : Prod G M) ↦
        @DFunLike.coe
          (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
            (@RingHom.id R (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
            M M (@AddCommGroup.toAddCommMonoid M inst_3) (@AddCommGroup.toAddCommMonoid M inst_3) inst_4 inst_4)
          M (fun (x : M) ↦ M)
          (@LinearMap.instFunLike R R M M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) (@AddCommGroup.toAddCommMonoid M inst_3)
            (@AddCommGroup.toAddCommMonoid M inst_3) inst_4 inst_4
            (@RingHom.id R (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
          (@DFunLike.coe
            (@Representation R G M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
              (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst_1)) (@AddCommGroup.toAddCommMonoid M inst_3) inst_4)
            G
            (fun (x : G) ↦
              @LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                (@RingHom.id R
                  (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                M M (@AddCommGroup.toAddCommMonoid M inst_3) (@AddCommGroup.toAddCommMonoid M inst_3) inst_4 inst_4)
            (@MonoidHom.instFunLike G
              (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                (@RingHom.id R
                  (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                M M (@AddCommGroup.toAddCommMonoid M inst_3) (@AddCommGroup.toAddCommMonoid M inst_3) inst_4 inst_4)
              (@MulOneClass.toMulOne G
                (@Monoid.toMulOneClass G (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst_1))))
              (@MulOneClass.toMulOne
                (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                  (@RingHom.id R
                    (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                  M M (@AddCommGroup.toAddCommMonoid M inst_3) (@AddCommGroup.toAddCommMonoid M inst_3) inst_4 inst_4)
                (@MulZeroOneClass.toMulOneClass
                  (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                    (@RingHom.id R
                      (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                    M M (@AddCommGroup.toAddCommMonoid M inst_3) (@AddCommGroup.toAddCommMonoid M inst_3) inst_4 inst_4)
                  (@instMulZeroOneClassOfSemiring
                    (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                      (@RingHom.id R
                        (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                      M M (@AddCommGroup.toAddCommMonoid M inst_3) (@AddCommGroup.toAddCommMonoid M inst_3) inst_4 inst_4)
                    (@Module.End.instSemiring R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                      (@AddCommGroup.toAddCommMonoid M inst_3) inst_4)))))
            rho (@Prod.fst G M p))
          (@Prod.snd G M p)

theorem UpperTheory.Reformulated.B.CoboundaryOfGenerator.aux2.{u_1, u_2, u_3} :
    ∀ {R : Type u_3} [inst : CommRing R] {G : Type u_1} [inst_1 : Group G] [inst_2 : TopologicalSpace G] {M : Type u_2}
      [inst_3 : AddCommGroup M]
      [inst_4 :
        @_root_.Module R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
          (@AddCommGroup.toAddCommMonoid M inst_3)]
      [inst_5 : TopologicalSpace M] [@IsTopologicalAddGroup M inst_5 (@AddCommGroup.toAddGroup M inst_3)]
      (rho :
        @Representation R G M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
          (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst_1)) (@AddCommGroup.toAddCommMonoid M inst_3) inst_4)
      {f f' : G → M},
      @Membership.mem (G → M) (Set (G → M)) (@Set.instMembership (G → M))
          (@Set.ofPred (G → M) fun (f : G → M) ↦
            And (@Continuous G M inst_2 inst_5 f)
              (∀ (g h : G),
                @Eq M
                  (f
                    (@HMul.hMul G G G
                      (@instHMul G
                        (@MulOne.toMul G
                          (@MulOneClass.toMulOne G
                            (@Monoid.toMulOneClass G (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst_1))))))
                      g h))
                  (@HAdd.hAdd M M M
                    (@instHAdd M
                      (@AddCommMagma.toAdd M
                        (@AddCommSemigroup.toAddCommMagma M
                          (@AddCommMonoid.toAddCommSemigroup M (@AddCommGroup.toAddCommMonoid M inst_3)))))
                    (f g)
                    (@DFunLike.coe
                      (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                        (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                        (@RingHom.id R
                          (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                        M M (@AddCommGroup.toAddCommMonoid M inst_3) (@AddCommGroup.toAddCommMonoid M inst_3) inst_4 inst_4)
                      M (fun (x : M) ↦ M)
                      (@LinearMap.instFunLike R R M M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                        (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                        (@AddCommGroup.toAddCommMonoid M inst_3) (@AddCommGroup.toAddCommMonoid M inst_3) inst_4 inst_4
                        (@RingHom.id R
                          (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
                      (@DFunLike.coe
                        (@Representation R G M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                          (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst_1))
                          (@AddCommGroup.toAddCommMonoid M inst_3) inst_4)
                        G
                        (fun (x : G) ↦
                          @LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                            (@RingHom.id R
                              (@Semiring.toNonAssocSemiring R
                                (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                            M M (@AddCommGroup.toAddCommMonoid M inst_3) (@AddCommGroup.toAddCommMonoid M inst_3) inst_4
                            inst_4)
                        (@MonoidHom.instFunLike G
                          (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                            (@RingHom.id R
                              (@Semiring.toNonAssocSemiring R
                                (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                            M M (@AddCommGroup.toAddCommMonoid M inst_3) (@AddCommGroup.toAddCommMonoid M inst_3) inst_4
                            inst_4)
                          (@MulOneClass.toMulOne G
                            (@Monoid.toMulOneClass G (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst_1))))
                          (@MulOneClass.toMulOne
                            (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@RingHom.id R
                                (@Semiring.toNonAssocSemiring R
                                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                              M M (@AddCommGroup.toAddCommMonoid M inst_3) (@AddCommGroup.toAddCommMonoid M inst_3) inst_4
                              inst_4)
                            (@MulZeroOneClass.toMulOneClass
                              (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@RingHom.id R
                                  (@Semiring.toNonAssocSemiring R
                                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                M M (@AddCommGroup.toAddCommMonoid M inst_3) (@AddCommGroup.toAddCommMonoid M inst_3) inst_4
                                inst_4)
                              (@instMulZeroOneClassOfSemiring
                                (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@RingHom.id R
                                    (@Semiring.toNonAssocSemiring R
                                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                  M M (@AddCommGroup.toAddCommMonoid M inst_3) (@AddCommGroup.toAddCommMonoid M inst_3)
                                  inst_4 inst_4)
                                (@Module.End.instSemiring R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@AddCommGroup.toAddCommMonoid M inst_3) inst_4)))))
                        rho g)
                      (f h)))))
          f →
        @Membership.mem (G → M) (Set (G → M)) (@Set.instMembership (G → M))
            (@Set.ofPred (G → M) fun (f : G → M) ↦
              And (@Continuous G M inst_2 inst_5 f)
                (∀ (g h : G),
                  @Eq M
                    (f
                      (@HMul.hMul G G G
                        (@instHMul G
                          (@MulOne.toMul G
                            (@MulOneClass.toMulOne G
                              (@Monoid.toMulOneClass G (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst_1))))))
                        g h))
                    (@HAdd.hAdd M M M
                      (@instHAdd M
                        (@AddCommMagma.toAdd M
                          (@AddCommSemigroup.toAddCommMagma M
                            (@AddCommMonoid.toAddCommSemigroup M (@AddCommGroup.toAddCommMonoid M inst_3)))))
                      (f g)
                      (@DFunLike.coe
                        (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                          (@RingHom.id R
                            (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                          M M (@AddCommGroup.toAddCommMonoid M inst_3) (@AddCommGroup.toAddCommMonoid M inst_3) inst_4
                          inst_4)
                        M (fun (x : M) ↦ M)
                        (@LinearMap.instFunLike R R M M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                          (@AddCommGroup.toAddCommMonoid M inst_3) (@AddCommGroup.toAddCommMonoid M inst_3) inst_4 inst_4
                          (@RingHom.id R
                            (@Semiring.toNonAssocSemiring R
                              (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
                        (@DFunLike.coe
                          (@Representation R G M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                            (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst_1))
                            (@AddCommGroup.toAddCommMonoid M inst_3) inst_4)
                          G
                          (fun (x : G) ↦
                            @LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@RingHom.id R
                                (@Semiring.toNonAssocSemiring R
                                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                              M M (@AddCommGroup.toAddCommMonoid M inst_3) (@AddCommGroup.toAddCommMonoid M inst_3) inst_4
                              inst_4)
                          (@MonoidHom.instFunLike G
                            (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@RingHom.id R
                                (@Semiring.toNonAssocSemiring R
                                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                              M M (@AddCommGroup.toAddCommMonoid M inst_3) (@AddCommGroup.toAddCommMonoid M inst_3) inst_4
                              inst_4)
                            (@MulOneClass.toMulOne G
                              (@Monoid.toMulOneClass G (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst_1))))
                            (@MulOneClass.toMulOne
                              (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@RingHom.id R
                                  (@Semiring.toNonAssocSemiring R
                                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                M M (@AddCommGroup.toAddCommMonoid M inst_3) (@AddCommGroup.toAddCommMonoid M inst_3) inst_4
                                inst_4)
                              (@MulZeroOneClass.toMulOneClass
                                (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@RingHom.id R
                                    (@Semiring.toNonAssocSemiring R
                                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                  M M (@AddCommGroup.toAddCommMonoid M inst_3) (@AddCommGroup.toAddCommMonoid M inst_3)
                                  inst_4 inst_4)
                                (@instMulZeroOneClassOfSemiring
                                  (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@RingHom.id R
                                      (@Semiring.toNonAssocSemiring R
                                        (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                    M M (@AddCommGroup.toAddCommMonoid M inst_3) (@AddCommGroup.toAddCommMonoid M inst_3)
                                    inst_4 inst_4)
                                  (@Module.End.instSemiring R M
                                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@AddCommGroup.toAddCommMonoid M inst_3) inst_4)))))
                          rho g)
                        (f h)))))
            f' →
          And
            (@Continuous G M inst_2 inst_5
              (@HAdd.hAdd (G → M) (G → M) (G → M)
                (@instHAdd (G → M)
                  (@AddZero.toAdd (G → M)
                    (@AddZeroClass.toAddZero (G → M)
                      (@AddMonoid.toAddZeroClass (G → M)
                        (@AddCommMonoid.toAddMonoid (G → M)
                          (@Pi.addCommMonoid G (fun (a : G) ↦ M) fun (i : G) ↦ @AddCommGroup.toAddCommMonoid M inst_3))))))
                f f'))
            (∀ (g h : G),
              @Eq M
                (@HAdd.hAdd (G → M) (G → M) (G → M)
                  (@instHAdd (G → M)
                    (@AddZero.toAdd (G → M)
                      (@AddZeroClass.toAddZero (G → M)
                        (@AddMonoid.toAddZeroClass (G → M)
                          (@AddCommMonoid.toAddMonoid (G → M)
                            (@Pi.addCommMonoid G (fun (a : G) ↦ M) fun (i : G) ↦
                              @AddCommGroup.toAddCommMonoid M inst_3))))))
                  f f'
                  (@HMul.hMul G G G
                    (@instHMul G
                      (@MulOne.toMul G
                        (@MulOneClass.toMulOne G
                          (@Monoid.toMulOneClass G (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst_1))))))
                    g h))
                (@HAdd.hAdd M M M
                  (@instHAdd M
                    (@AddCommMagma.toAdd M
                      (@AddCommSemigroup.toAddCommMagma M
                        (@AddCommMonoid.toAddCommSemigroup M (@AddCommGroup.toAddCommMonoid M inst_3)))))
                  (@HAdd.hAdd (G → M) (G → M) (G → M)
                    (@instHAdd (G → M)
                      (@AddZero.toAdd (G → M)
                        (@AddZeroClass.toAddZero (G → M)
                          (@AddMonoid.toAddZeroClass (G → M)
                            (@AddCommMonoid.toAddMonoid (G → M)
                              (@Pi.addCommMonoid G (fun (a : G) ↦ M) fun (i : G) ↦
                                @AddCommGroup.toAddCommMonoid M inst_3))))))
                    f f' g)
                  (@DFunLike.coe
                    (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                      (@RingHom.id R
                        (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                      M M (@AddCommGroup.toAddCommMonoid M inst_3) (@AddCommGroup.toAddCommMonoid M inst_3) inst_4 inst_4)
                    M (fun (x : M) ↦ M)
                    (@LinearMap.instFunLike R R M M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                      (@AddCommGroup.toAddCommMonoid M inst_3) (@AddCommGroup.toAddCommMonoid M inst_3) inst_4 inst_4
                      (@RingHom.id R
                        (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
                    (@DFunLike.coe
                      (@Representation R G M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                        (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst_1)) (@AddCommGroup.toAddCommMonoid M inst_3)
                        inst_4)
                      G
                      (fun (x : G) ↦
                        @LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                          (@RingHom.id R
                            (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                          M M (@AddCommGroup.toAddCommMonoid M inst_3) (@AddCommGroup.toAddCommMonoid M inst_3) inst_4
                          inst_4)
                      (@MonoidHom.instFunLike G
                        (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                          (@RingHom.id R
                            (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                          M M (@AddCommGroup.toAddCommMonoid M inst_3) (@AddCommGroup.toAddCommMonoid M inst_3) inst_4
                          inst_4)
                        (@MulOneClass.toMulOne G
                          (@Monoid.toMulOneClass G (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst_1))))
                        (@MulOneClass.toMulOne
                          (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                            (@RingHom.id R
                              (@Semiring.toNonAssocSemiring R
                                (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                            M M (@AddCommGroup.toAddCommMonoid M inst_3) (@AddCommGroup.toAddCommMonoid M inst_3) inst_4
                            inst_4)
                          (@MulZeroOneClass.toMulOneClass
                            (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@RingHom.id R
                                (@Semiring.toNonAssocSemiring R
                                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                              M M (@AddCommGroup.toAddCommMonoid M inst_3) (@AddCommGroup.toAddCommMonoid M inst_3) inst_4
                              inst_4)
                            (@instMulZeroOneClassOfSemiring
                              (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@RingHom.id R
                                  (@Semiring.toNonAssocSemiring R
                                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                M M (@AddCommGroup.toAddCommMonoid M inst_3) (@AddCommGroup.toAddCommMonoid M inst_3) inst_4
                                inst_4)
                              (@Module.End.instSemiring R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@AddCommGroup.toAddCommMonoid M inst_3) inst_4)))))
                      rho g)
                    (@HAdd.hAdd (G → M) (G → M) (G → M)
                      (@instHAdd (G → M)
                        (@AddZero.toAdd (G → M)
                          (@AddZeroClass.toAddZero (G → M)
                            (@AddMonoid.toAddZeroClass (G → M)
                              (@AddCommMonoid.toAddMonoid (G → M)
                                (@Pi.addCommMonoid G (fun (a : G) ↦ M) fun (i : G) ↦
                                  @AddCommGroup.toAddCommMonoid M inst_3))))))
                      f f' h)))) := by
  intro R _ G _ _ M _ _ _ _ rho f f' hf hf'
  obtain ⟨hc, hf⟩ := hf
  obtain ⟨hc', hf'⟩ := hf'
  refine ⟨hc.add hc', fun g h => ?_⟩
  simp only [Pi.add_apply, hf g h, hf' g h, map_add]
  abel

theorem UpperTheory.Reformulated.B.CoboundaryOfGenerator.aux3.{u_1, u_2, u_3} :
    ∀ {R : Type u_3} [inst : CommRing R] {G : Type u_1} [inst_1 : Group G] [inst_2 : TopologicalSpace G] {M : Type u_2}
      [inst_3 : AddCommGroup M]
      [inst_4 :
        @_root_.Module R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
          (@AddCommGroup.toAddCommMonoid M inst_3)]
      [inst_5 : TopologicalSpace M]
      (rho :
        @Representation R G M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
          (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst_1)) (@AddCommGroup.toAddCommMonoid M inst_3) inst_4),
      And
        (@Continuous G M inst_2 inst_5
          (@OfNat.ofNat (G → M) (nat_lit 0)
            (@Zero.toOfNat0 (G → M)
              (@AddZero.toZero (G → M)
                (@AddZeroClass.toAddZero (G → M)
                  (@AddMonoid.toAddZeroClass (G → M)
                    (@AddCommMonoid.toAddMonoid (G → M)
                      (@Pi.addCommMonoid G (fun (a : G) ↦ M) fun (i : G) ↦ @AddCommGroup.toAddCommMonoid M inst_3))))))))
        (∀ (g h : G),
          @Eq M
            (@OfNat.ofNat (G → M) (nat_lit 0)
              (@Zero.toOfNat0 (G → M)
                (@AddZero.toZero (G → M)
                  (@AddZeroClass.toAddZero (G → M)
                    (@AddMonoid.toAddZeroClass (G → M)
                      (@AddCommMonoid.toAddMonoid (G → M)
                        (@Pi.addCommMonoid G (fun (a : G) ↦ M) fun (i : G) ↦ @AddCommGroup.toAddCommMonoid M inst_3))))))
              (@HMul.hMul G G G
                (@instHMul G
                  (@MulOne.toMul G
                    (@MulOneClass.toMulOne G
                      (@Monoid.toMulOneClass G (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst_1))))))
                g h))
            (@HAdd.hAdd M M M
              (@instHAdd M
                (@AddCommMagma.toAdd M
                  (@AddCommSemigroup.toAddCommMagma M
                    (@AddCommMonoid.toAddCommSemigroup M (@AddCommGroup.toAddCommMonoid M inst_3)))))
              (@OfNat.ofNat (G → M) (nat_lit 0)
                (@Zero.toOfNat0 (G → M)
                  (@AddZero.toZero (G → M)
                    (@AddZeroClass.toAddZero (G → M)
                      (@AddMonoid.toAddZeroClass (G → M)
                        (@AddCommMonoid.toAddMonoid (G → M)
                          (@Pi.addCommMonoid G (fun (a : G) ↦ M) fun (i : G) ↦ @AddCommGroup.toAddCommMonoid M inst_3))))))
                g)
              (@DFunLike.coe
                (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                  (@RingHom.id R
                    (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                  M M (@AddCommGroup.toAddCommMonoid M inst_3) (@AddCommGroup.toAddCommMonoid M inst_3) inst_4 inst_4)
                M (fun (x : M) ↦ M)
                (@LinearMap.instFunLike R R M M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) (@AddCommGroup.toAddCommMonoid M inst_3)
                  (@AddCommGroup.toAddCommMonoid M inst_3) inst_4 inst_4
                  (@RingHom.id R
                    (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
                (@DFunLike.coe
                  (@Representation R G M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                    (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst_1)) (@AddCommGroup.toAddCommMonoid M inst_3)
                    inst_4)
                  G
                  (fun (x : G) ↦
                    @LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                      (@RingHom.id R
                        (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                      M M (@AddCommGroup.toAddCommMonoid M inst_3) (@AddCommGroup.toAddCommMonoid M inst_3) inst_4 inst_4)
                  (@MonoidHom.instFunLike G
                    (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                      (@RingHom.id R
                        (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                      M M (@AddCommGroup.toAddCommMonoid M inst_3) (@AddCommGroup.toAddCommMonoid M inst_3) inst_4 inst_4)
                    (@MulOneClass.toMulOne G
                      (@Monoid.toMulOneClass G (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst_1))))
                    (@MulOneClass.toMulOne
                      (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                        (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                        (@RingHom.id R
                          (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                        M M (@AddCommGroup.toAddCommMonoid M inst_3) (@AddCommGroup.toAddCommMonoid M inst_3) inst_4 inst_4)
                      (@MulZeroOneClass.toMulOneClass
                        (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                          (@RingHom.id R
                            (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                          M M (@AddCommGroup.toAddCommMonoid M inst_3) (@AddCommGroup.toAddCommMonoid M inst_3) inst_4
                          inst_4)
                        (@instMulZeroOneClassOfSemiring
                          (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                            (@RingHom.id R
                              (@Semiring.toNonAssocSemiring R
                                (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                            M M (@AddCommGroup.toAddCommMonoid M inst_3) (@AddCommGroup.toAddCommMonoid M inst_3) inst_4
                            inst_4)
                          (@Module.End.instSemiring R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                            (@AddCommGroup.toAddCommMonoid M inst_3) inst_4)))))
                  rho g)
                (@OfNat.ofNat (G → M) (nat_lit 0)
                  (@Zero.toOfNat0 (G → M)
                    (@AddZero.toZero (G → M)
                      (@AddZeroClass.toAddZero (G → M)
                        (@AddMonoid.toAddZeroClass (G → M)
                          (@AddCommMonoid.toAddMonoid (G → M)
                            (@Pi.addCommMonoid G (fun (a : G) ↦ M) fun (i : G) ↦
                              @AddCommGroup.toAddCommMonoid M inst_3))))))
                  h)))) := by
  intro R _ G _ _ M _ _ _ rho
  exact ⟨continuous_const, fun g h => by simp⟩

theorem UpperTheory.Reformulated.B.CoboundaryOfGenerator.aux4.{u_1, u_2, u_3} :
    ∀ {R : Type u_3} [inst : CommRing R] {G : Type u_1} [inst_1 : Group G] [inst_2 : TopologicalSpace G] {M : Type u_2}
      [inst_3 : AddCommGroup M]
      [inst_4 :
        @_root_.Module R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
          (@AddCommGroup.toAddCommMonoid M inst_3)]
      [inst_5 : TopologicalSpace M]
      [@ContinuousConstSMul R M inst_5
          (@SMulZeroClass.toSMul R M
            (@AddZero.toZero M
              (@AddZeroClass.toAddZero M
                (@AddMonoid.toAddZeroClass M
                  (@SubNegMonoid.toAddMonoid M (@AddGroup.toSubNegMonoid M (@AddCommGroup.toAddGroup M inst_3))))))
            (@DistribSMul.toSMulZeroClass R M
              (@AddMonoid.toAddZeroClass M
                (@SubNegMonoid.toAddMonoid M (@AddGroup.toSubNegMonoid M (@AddCommGroup.toAddGroup M inst_3))))
              (@DistribMulAction.toDistribSMul R M
                (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                (@SubNegMonoid.toAddMonoid M (@AddGroup.toSubNegMonoid M (@AddCommGroup.toAddGroup M inst_3)))
                (@Module.toDistribMulAction R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                  (@AddCommGroup.toAddCommMonoid M inst_3) inst_4))))]
      (rho :
        @Representation R G M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
          (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst_1)) (@AddCommGroup.toAddCommMonoid M inst_3) inst_4)
      (c : R) (f : G → M),
      @Membership.mem (G → M) (Set (G → M)) (@Set.instMembership (G → M))
          (@Set.ofPred (G → M) fun (f : G → M) ↦
            And (@Continuous G M inst_2 inst_5 f)
              (∀ (g h : G),
                @Eq M
                  (f
                    (@HMul.hMul G G G
                      (@instHMul G
                        (@MulOne.toMul G
                          (@MulOneClass.toMulOne G
                            (@Monoid.toMulOneClass G (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst_1))))))
                      g h))
                  (@HAdd.hAdd M M M
                    (@instHAdd M
                      (@AddCommMagma.toAdd M
                        (@AddCommSemigroup.toAddCommMagma M
                          (@AddCommMonoid.toAddCommSemigroup M (@AddCommGroup.toAddCommMonoid M inst_3)))))
                    (f g)
                    (@DFunLike.coe
                      (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                        (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                        (@RingHom.id R
                          (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                        M M (@AddCommGroup.toAddCommMonoid M inst_3) (@AddCommGroup.toAddCommMonoid M inst_3) inst_4 inst_4)
                      M (fun (x : M) ↦ M)
                      (@LinearMap.instFunLike R R M M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                        (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                        (@AddCommGroup.toAddCommMonoid M inst_3) (@AddCommGroup.toAddCommMonoid M inst_3) inst_4 inst_4
                        (@RingHom.id R
                          (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
                      (@DFunLike.coe
                        (@Representation R G M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                          (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst_1))
                          (@AddCommGroup.toAddCommMonoid M inst_3) inst_4)
                        G
                        (fun (x : G) ↦
                          @LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                            (@RingHom.id R
                              (@Semiring.toNonAssocSemiring R
                                (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                            M M (@AddCommGroup.toAddCommMonoid M inst_3) (@AddCommGroup.toAddCommMonoid M inst_3) inst_4
                            inst_4)
                        (@MonoidHom.instFunLike G
                          (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                            (@RingHom.id R
                              (@Semiring.toNonAssocSemiring R
                                (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                            M M (@AddCommGroup.toAddCommMonoid M inst_3) (@AddCommGroup.toAddCommMonoid M inst_3) inst_4
                            inst_4)
                          (@MulOneClass.toMulOne G
                            (@Monoid.toMulOneClass G (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst_1))))
                          (@MulOneClass.toMulOne
                            (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@RingHom.id R
                                (@Semiring.toNonAssocSemiring R
                                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                              M M (@AddCommGroup.toAddCommMonoid M inst_3) (@AddCommGroup.toAddCommMonoid M inst_3) inst_4
                              inst_4)
                            (@MulZeroOneClass.toMulOneClass
                              (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@RingHom.id R
                                  (@Semiring.toNonAssocSemiring R
                                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                M M (@AddCommGroup.toAddCommMonoid M inst_3) (@AddCommGroup.toAddCommMonoid M inst_3) inst_4
                                inst_4)
                              (@instMulZeroOneClassOfSemiring
                                (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@RingHom.id R
                                    (@Semiring.toNonAssocSemiring R
                                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                  M M (@AddCommGroup.toAddCommMonoid M inst_3) (@AddCommGroup.toAddCommMonoid M inst_3)
                                  inst_4 inst_4)
                                (@Module.End.instSemiring R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@AddCommGroup.toAddCommMonoid M inst_3) inst_4)))))
                        rho g)
                      (f h)))))
          f →
        And
          (@Continuous G M inst_2 inst_5
            (@HSMul.hSMul R (G → M) (G → M)
              (@instHSMul R (G → M)
                (@SMulZeroClass.toSMul R (G → M)
                  (@AddZero.toZero (G → M)
                    (@AddZeroClass.toAddZero (G → M)
                      (@AddMonoid.toAddZeroClass (G → M)
                        (@AddCommMonoid.toAddMonoid (G → M)
                          (@Pi.addCommMonoid G (fun (a : G) ↦ M) fun (i : G) ↦ @AddCommGroup.toAddCommMonoid M inst_3)))))
                  (@DistribSMul.toSMulZeroClass R (G → M)
                    (@AddMonoid.toAddZeroClass (G → M)
                      (@AddCommMonoid.toAddMonoid (G → M)
                        (@Pi.addCommMonoid G (fun (a : G) ↦ M) fun (i : G) ↦ @AddCommGroup.toAddCommMonoid M inst_3)))
                    (@DistribMulAction.toDistribSMul R (G → M)
                      (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                      (@AddCommMonoid.toAddMonoid (G → M)
                        (@Pi.addCommMonoid G (fun (a : G) ↦ M) fun (i : G) ↦ @AddCommGroup.toAddCommMonoid M inst_3))
                      (@Module.toDistribMulAction R (G → M) (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                        (@Pi.addCommMonoid G (fun (a : G) ↦ M) fun (i : G) ↦ @AddCommGroup.toAddCommMonoid M inst_3)
                        (@Pi.Function.module G R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                          (@AddCommGroup.toAddCommMonoid M inst_3) inst_4))))))
              c f))
          (∀ (g h : G),
            @Eq M
              (@HSMul.hSMul R (G → M) (G → M)
                (@instHSMul R (G → M)
                  (@SMulZeroClass.toSMul R (G → M)
                    (@AddZero.toZero (G → M)
                      (@AddZeroClass.toAddZero (G → M)
                        (@AddMonoid.toAddZeroClass (G → M)
                          (@AddCommMonoid.toAddMonoid (G → M)
                            (@Pi.addCommMonoid G (fun (a : G) ↦ M) fun (i : G) ↦ @AddCommGroup.toAddCommMonoid M inst_3)))))
                    (@DistribSMul.toSMulZeroClass R (G → M)
                      (@AddMonoid.toAddZeroClass (G → M)
                        (@AddCommMonoid.toAddMonoid (G → M)
                          (@Pi.addCommMonoid G (fun (a : G) ↦ M) fun (i : G) ↦ @AddCommGroup.toAddCommMonoid M inst_3)))
                      (@DistribMulAction.toDistribSMul R (G → M)
                        (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                        (@AddCommMonoid.toAddMonoid (G → M)
                          (@Pi.addCommMonoid G (fun (a : G) ↦ M) fun (i : G) ↦ @AddCommGroup.toAddCommMonoid M inst_3))
                        (@Module.toDistribMulAction R (G → M) (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                          (@Pi.addCommMonoid G (fun (a : G) ↦ M) fun (i : G) ↦ @AddCommGroup.toAddCommMonoid M inst_3)
                          (@Pi.Function.module G R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                            (@AddCommGroup.toAddCommMonoid M inst_3) inst_4))))))
                c f
                (@HMul.hMul G G G
                  (@instHMul G
                    (@MulOne.toMul G
                      (@MulOneClass.toMulOne G
                        (@Monoid.toMulOneClass G (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst_1))))))
                  g h))
              (@HAdd.hAdd M M M
                (@instHAdd M
                  (@AddCommMagma.toAdd M
                    (@AddCommSemigroup.toAddCommMagma M
                      (@AddCommMonoid.toAddCommSemigroup M (@AddCommGroup.toAddCommMonoid M inst_3)))))
                (@HSMul.hSMul R (G → M) (G → M)
                  (@instHSMul R (G → M)
                    (@SMulZeroClass.toSMul R (G → M)
                      (@AddZero.toZero (G → M)
                        (@AddZeroClass.toAddZero (G → M)
                          (@AddMonoid.toAddZeroClass (G → M)
                            (@AddCommMonoid.toAddMonoid (G → M)
                              (@Pi.addCommMonoid G (fun (a : G) ↦ M) fun (i : G) ↦
                                @AddCommGroup.toAddCommMonoid M inst_3)))))
                      (@DistribSMul.toSMulZeroClass R (G → M)
                        (@AddMonoid.toAddZeroClass (G → M)
                          (@AddCommMonoid.toAddMonoid (G → M)
                            (@Pi.addCommMonoid G (fun (a : G) ↦ M) fun (i : G) ↦ @AddCommGroup.toAddCommMonoid M inst_3)))
                        (@DistribMulAction.toDistribSMul R (G → M)
                          (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                          (@AddCommMonoid.toAddMonoid (G → M)
                            (@Pi.addCommMonoid G (fun (a : G) ↦ M) fun (i : G) ↦ @AddCommGroup.toAddCommMonoid M inst_3))
                          (@Module.toDistribMulAction R (G → M)
                            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                            (@Pi.addCommMonoid G (fun (a : G) ↦ M) fun (i : G) ↦ @AddCommGroup.toAddCommMonoid M inst_3)
                            (@Pi.Function.module G R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@AddCommGroup.toAddCommMonoid M inst_3) inst_4))))))
                  c f g)
                (@DFunLike.coe
                  (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                    (@RingHom.id R
                      (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                    M M (@AddCommGroup.toAddCommMonoid M inst_3) (@AddCommGroup.toAddCommMonoid M inst_3) inst_4 inst_4)
                  M (fun (x : M) ↦ M)
                  (@LinearMap.instFunLike R R M M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) (@AddCommGroup.toAddCommMonoid M inst_3)
                    (@AddCommGroup.toAddCommMonoid M inst_3) inst_4 inst_4
                    (@RingHom.id R
                      (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
                  (@DFunLike.coe
                    (@Representation R G M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                      (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst_1)) (@AddCommGroup.toAddCommMonoid M inst_3)
                      inst_4)
                    G
                    (fun (x : G) ↦
                      @LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                        (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                        (@RingHom.id R
                          (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                        M M (@AddCommGroup.toAddCommMonoid M inst_3) (@AddCommGroup.toAddCommMonoid M inst_3) inst_4 inst_4)
                    (@MonoidHom.instFunLike G
                      (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                        (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                        (@RingHom.id R
                          (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                        M M (@AddCommGroup.toAddCommMonoid M inst_3) (@AddCommGroup.toAddCommMonoid M inst_3) inst_4 inst_4)
                      (@MulOneClass.toMulOne G
                        (@Monoid.toMulOneClass G (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst_1))))
                      (@MulOneClass.toMulOne
                        (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                          (@RingHom.id R
                            (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                          M M (@AddCommGroup.toAddCommMonoid M inst_3) (@AddCommGroup.toAddCommMonoid M inst_3) inst_4
                          inst_4)
                        (@MulZeroOneClass.toMulOneClass
                          (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                            (@RingHom.id R
                              (@Semiring.toNonAssocSemiring R
                                (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                            M M (@AddCommGroup.toAddCommMonoid M inst_3) (@AddCommGroup.toAddCommMonoid M inst_3) inst_4
                            inst_4)
                          (@instMulZeroOneClassOfSemiring
                            (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@RingHom.id R
                                (@Semiring.toNonAssocSemiring R
                                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                              M M (@AddCommGroup.toAddCommMonoid M inst_3) (@AddCommGroup.toAddCommMonoid M inst_3) inst_4
                              inst_4)
                            (@Module.End.instSemiring R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@AddCommGroup.toAddCommMonoid M inst_3) inst_4)))))
                    rho g)
                  (@HSMul.hSMul R (G → M) (G → M)
                    (@instHSMul R (G → M)
                      (@SMulZeroClass.toSMul R (G → M)
                        (@AddZero.toZero (G → M)
                          (@AddZeroClass.toAddZero (G → M)
                            (@AddMonoid.toAddZeroClass (G → M)
                              (@AddCommMonoid.toAddMonoid (G → M)
                                (@Pi.addCommMonoid G (fun (a : G) ↦ M) fun (i : G) ↦
                                  @AddCommGroup.toAddCommMonoid M inst_3)))))
                        (@DistribSMul.toSMulZeroClass R (G → M)
                          (@AddMonoid.toAddZeroClass (G → M)
                            (@AddCommMonoid.toAddMonoid (G → M)
                              (@Pi.addCommMonoid G (fun (a : G) ↦ M) fun (i : G) ↦ @AddCommGroup.toAddCommMonoid M inst_3)))
                          (@DistribMulAction.toDistribSMul R (G → M)
                            (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                            (@AddCommMonoid.toAddMonoid (G → M)
                              (@Pi.addCommMonoid G (fun (a : G) ↦ M) fun (i : G) ↦ @AddCommGroup.toAddCommMonoid M inst_3))
                            (@Module.toDistribMulAction R (G → M)
                              (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@Pi.addCommMonoid G (fun (a : G) ↦ M) fun (i : G) ↦ @AddCommGroup.toAddCommMonoid M inst_3)
                              (@Pi.Function.module G R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@AddCommGroup.toAddCommMonoid M inst_3) inst_4))))))
                    c f h)))) := by
  intro R _ G _ _ M _ _ _ _ rho c f hf
  obtain ⟨hc, hf⟩ := hf
  refine ⟨hc.const_smul c, fun g h => ?_⟩
  simp only [Pi.smul_apply, hf g h, map_smul, smul_add]

noncomputable def UpperTheory.Reformulated.B.CoboundaryOfGenerator.Z1.{u_1, u_2, u_3} :
    {R : Type u_1} →
      [inst : CommRing R] →
        {G : Type u_2} →
          [inst_1 : Group G] →
            [TopologicalSpace G] →
              {M : Type u_3} →
                [inst_3 : AddCommGroup M] →
                  [inst_4 :
                      @_root_.Module R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                        (@AddCommGroup.toAddCommMonoid M inst_3)] →
                    [inst_5 : TopologicalSpace M] →
                      [@IsTopologicalAddGroup M inst_5 (@AddCommGroup.toAddGroup M inst_3)] →
                        [@ContinuousConstSMul R M inst_5
                              (@SMulZeroClass.toSMul R M
                                (@AddZero.toZero M
                                  (@AddZeroClass.toAddZero M
                                    (@AddMonoid.toAddZeroClass M
                                      (@SubNegMonoid.toAddMonoid M
                                        (@AddGroup.toSubNegMonoid M (@AddCommGroup.toAddGroup M inst_3))))))
                                (@DistribSMul.toSMulZeroClass R M
                                  (@AddMonoid.toAddZeroClass M
                                    (@SubNegMonoid.toAddMonoid M
                                      (@AddGroup.toSubNegMonoid M (@AddCommGroup.toAddGroup M inst_3))))
                                  (@DistribMulAction.toDistribSMul R M
                                    (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                    (@SubNegMonoid.toAddMonoid M
                                      (@AddGroup.toSubNegMonoid M (@AddCommGroup.toAddGroup M inst_3)))
                                    (@Module.toDistribMulAction R M
                                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                      (@AddCommGroup.toAddCommMonoid M inst_3) inst_4))))] →
                          @Representation R G M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst_1))
                              (@AddCommGroup.toAddCommMonoid M inst_3) inst_4 →
                            @Submodule R (G → M) (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@Pi.addCommMonoid G (fun (a : G) ↦ M) fun (i : G) ↦ @AddCommGroup.toAddCommMonoid M inst_3)
                              (@Pi.Function.module G R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@AddCommGroup.toAddCommMonoid M inst_3) inst_4) :=
    fun {R : Type u_1} [inst : CommRing R] {G : Type u_2} [inst_1 : Group G] [inst_2 : TopologicalSpace G] {M : Type u_3}
        [inst_3 : AddCommGroup M]
        [inst_4 :
          @_root_.Module R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
            (@AddCommGroup.toAddCommMonoid M inst_3)]
        [inst_5 : TopologicalSpace M] [inst_6 : @IsTopologicalAddGroup M inst_5 (@AddCommGroup.toAddGroup M inst_3)]
        [inst_7 :
          @ContinuousConstSMul R M inst_5
            (@SMulZeroClass.toSMul R M
              (@AddZero.toZero M
                (@AddZeroClass.toAddZero M
                  (@AddMonoid.toAddZeroClass M
                    (@SubNegMonoid.toAddMonoid M (@AddGroup.toSubNegMonoid M (@AddCommGroup.toAddGroup M inst_3))))))
              (@DistribSMul.toSMulZeroClass R M
                (@AddMonoid.toAddZeroClass M
                  (@SubNegMonoid.toAddMonoid M (@AddGroup.toSubNegMonoid M (@AddCommGroup.toAddGroup M inst_3))))
                (@DistribMulAction.toDistribSMul R M
                  (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                  (@SubNegMonoid.toAddMonoid M (@AddGroup.toSubNegMonoid M (@AddCommGroup.toAddGroup M inst_3)))
                  (@Module.toDistribMulAction R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                    (@AddCommGroup.toAddCommMonoid M inst_3) inst_4))))]
        (rho :
          @Representation R G M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
            (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst_1)) (@AddCommGroup.toAddCommMonoid M inst_3) inst_4) ↦
      @Submodule.mk R (G → M) (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
        (@Pi.addCommMonoid G (fun (a : G) ↦ M) fun (i : G) ↦ @AddCommGroup.toAddCommMonoid M inst_3)
        (@Pi.Function.module G R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
          (@AddCommGroup.toAddCommMonoid M inst_3) inst_4)
        (@AddSubmonoid.mk (G → M)
          (@AddMonoid.toAddZeroClass (G → M)
            (@AddCommMonoid.toAddMonoid (G → M)
              (@Pi.addCommMonoid G (fun (a : G) ↦ M) fun (i : G) ↦ @AddCommGroup.toAddCommMonoid M inst_3)))
          (@AddSubsemigroup.mk (G → M)
            (@AddZero.toAdd (G → M)
              (@AddZeroClass.toAddZero (G → M)
                (@AddMonoid.toAddZeroClass (G → M)
                  (@AddCommMonoid.toAddMonoid (G → M)
                    (@Pi.addCommMonoid G (fun (a : G) ↦ M) fun (i : G) ↦ @AddCommGroup.toAddCommMonoid M inst_3)))))
            (@Set.ofPred (G → M) fun (f : G → M) ↦
              And (@Continuous G M inst_2 inst_5 f)
                (∀ (g h : G),
                  @Eq M
                    (f
                      (@HMul.hMul G G G
                        (@instHMul G
                          (@MulOne.toMul G
                            (@MulOneClass.toMulOne G
                              (@Monoid.toMulOneClass G (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst_1))))))
                        g h))
                    (@HAdd.hAdd M M M
                      (@instHAdd M
                        (@AddCommMagma.toAdd M
                          (@AddCommSemigroup.toAddCommMagma M
                            (@AddCommMonoid.toAddCommSemigroup M (@AddCommGroup.toAddCommMonoid M inst_3)))))
                      (f g)
                      (@DFunLike.coe
                        (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                          (@RingHom.id R
                            (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                          M M (@AddCommGroup.toAddCommMonoid M inst_3) (@AddCommGroup.toAddCommMonoid M inst_3) inst_4
                          inst_4)
                        M (fun (x : M) ↦ M)
                        (@LinearMap.instFunLike R R M M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                          (@AddCommGroup.toAddCommMonoid M inst_3) (@AddCommGroup.toAddCommMonoid M inst_3) inst_4 inst_4
                          (@RingHom.id R
                            (@Semiring.toNonAssocSemiring R
                              (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
                        (@DFunLike.coe
                          (@Representation R G M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                            (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst_1))
                            (@AddCommGroup.toAddCommMonoid M inst_3) inst_4)
                          G
                          (fun (x : G) ↦
                            @LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@RingHom.id R
                                (@Semiring.toNonAssocSemiring R
                                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                              M M (@AddCommGroup.toAddCommMonoid M inst_3) (@AddCommGroup.toAddCommMonoid M inst_3) inst_4
                              inst_4)
                          (@MonoidHom.instFunLike G
                            (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@RingHom.id R
                                (@Semiring.toNonAssocSemiring R
                                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                              M M (@AddCommGroup.toAddCommMonoid M inst_3) (@AddCommGroup.toAddCommMonoid M inst_3) inst_4
                              inst_4)
                            (@MulOneClass.toMulOne G
                              (@Monoid.toMulOneClass G (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst_1))))
                            (@MulOneClass.toMulOne
                              (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@RingHom.id R
                                  (@Semiring.toNonAssocSemiring R
                                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                M M (@AddCommGroup.toAddCommMonoid M inst_3) (@AddCommGroup.toAddCommMonoid M inst_3) inst_4
                                inst_4)
                              (@MulZeroOneClass.toMulOneClass
                                (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@RingHom.id R
                                    (@Semiring.toNonAssocSemiring R
                                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                  M M (@AddCommGroup.toAddCommMonoid M inst_3) (@AddCommGroup.toAddCommMonoid M inst_3)
                                  inst_4 inst_4)
                                (@instMulZeroOneClassOfSemiring
                                  (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@RingHom.id R
                                      (@Semiring.toNonAssocSemiring R
                                        (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                    M M (@AddCommGroup.toAddCommMonoid M inst_3) (@AddCommGroup.toAddCommMonoid M inst_3)
                                    inst_4 inst_4)
                                  (@Module.End.instSemiring R M
                                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@AddCommGroup.toAddCommMonoid M inst_3) inst_4)))))
                          rho g)
                        (f h)))))
            (@UpperTheory.Reformulated.B.CoboundaryOfGenerator.aux2 R inst G inst_1 inst_2 M inst_3 inst_4 inst_5 inst_6 rho))
          (@UpperTheory.Reformulated.B.CoboundaryOfGenerator.aux3 R inst G inst_1 inst_2 M inst_3 inst_4 inst_5 rho))
        (@UpperTheory.Reformulated.B.CoboundaryOfGenerator.aux4 R inst G inst_1 inst_2 M inst_3 inst_4 inst_5 inst_7 rho)

theorem UpperTheory.Reformulated.B.CoboundaryOfGenerator.aux6.{u_1, u_2} :
    ∀ {R : Type u_1} {M : Type u_2} [inst : SMul R M] [inst_1 : TopologicalSpace M] [@DiscreteTopology M inst_1],
      @ContinuousConstSMul R M inst_1 inst := by
  intro R M _ _ _
  exact ⟨fun _ => continuous_of_discreteTopology⟩

theorem UpperTheory.Reformulated.B.CoboundaryOfGenerator.aux7.{u_1} :
    ∀ {R : Type u_1} [inst : CommRing R],
      @RingHomSurjective R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
        (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
        (@RingHom.id R (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))) := by
  intro R _
  exact ⟨Function.surjective_id⟩

noncomputable def UpperTheory.Reformulated.B.CoboundaryOfGenerator.d0.{u_1, u_2, u_3} :
    {R : Type u_1} →
      [inst : CommRing R] →
        {G : Type u_2} →
          [inst_1 : Group G] →
            {M : Type u_3} →
              [inst_2 : AddCommGroup M] →
                [inst_3 :
                    @_root_.Module R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                      (@AddCommGroup.toAddCommMonoid M inst_2)] →
                  @Representation R G M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                      (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst_1)) (@AddCommGroup.toAddCommMonoid M inst_2)
                      inst_3 →
                    @LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                      (@RingHom.id R
                        (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                      M (G → M) (@AddCommGroup.toAddCommMonoid M inst_2)
                      (@Pi.addCommMonoid G (fun (a : G) ↦ M) fun (i : G) ↦ @AddCommGroup.toAddCommMonoid M inst_2) inst_3
                      (@Pi.Function.module G R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                        (@AddCommGroup.toAddCommMonoid M inst_2) inst_3) :=
    fun {R : Type u_1} [inst : CommRing R] {G : Type u_2} [inst_1 : Group G] {M : Type u_3} [inst_2 : AddCommGroup M]
        [inst_3 :
          @_root_.Module R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
            (@AddCommGroup.toAddCommMonoid M inst_2)]
        (rho :
          @Representation R G M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
            (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst_1)) (@AddCommGroup.toAddCommMonoid M inst_2) inst_3) ↦
      @LinearMap.pi R M G (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
        (@AddCommGroup.toAddCommMonoid M inst_2) inst_3 (fun (a : G) ↦ M)
        (fun (i : G) ↦ @AddCommGroup.toAddCommMonoid M inst_2) (fun (i : G) ↦ inst_3) fun (g : G) ↦
        @HSub.hSub
          (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
            (@RingHom.id R (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
            M M (@AddCommGroup.toAddCommMonoid M inst_2) (@AddCommGroup.toAddCommMonoid M inst_2) inst_3 inst_3)
          (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
            (@RingHom.id R (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
            M M (@AddCommGroup.toAddCommMonoid M inst_2) (@AddCommGroup.toAddCommMonoid M inst_2) inst_3 inst_3)
          (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
            (@RingHom.id R (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
            M M (@AddCommGroup.toAddCommMonoid M inst_2) (@AddCommGroup.toAddCommMonoid M inst_2) inst_3 inst_3)
          (@instHSub
            (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
              (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
              (@RingHom.id R
                (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
              M M (@AddCommGroup.toAddCommMonoid M inst_2) (@AddCommGroup.toAddCommMonoid M inst_2) inst_3 inst_3)
            (@LinearMap.instSub R R M M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
              (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) (@AddCommGroup.toAddCommMonoid M inst_2) inst_2
              inst_3 inst_3
              (@RingHom.id R
                (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))))
          (@DFunLike.coe
            (@Representation R G M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
              (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst_1)) (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
            G
            (fun (x : G) ↦
              @LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                (@RingHom.id R
                  (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                M M (@AddCommGroup.toAddCommMonoid M inst_2) (@AddCommGroup.toAddCommMonoid M inst_2) inst_3 inst_3)
            (@MonoidHom.instFunLike G
              (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                (@RingHom.id R
                  (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                M M (@AddCommGroup.toAddCommMonoid M inst_2) (@AddCommGroup.toAddCommMonoid M inst_2) inst_3 inst_3)
              (@MulOneClass.toMulOne G
                (@Monoid.toMulOneClass G (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst_1))))
              (@MulOneClass.toMulOne
                (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                  (@RingHom.id R
                    (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                  M M (@AddCommGroup.toAddCommMonoid M inst_2) (@AddCommGroup.toAddCommMonoid M inst_2) inst_3 inst_3)
                (@MulZeroOneClass.toMulOneClass
                  (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                    (@RingHom.id R
                      (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                    M M (@AddCommGroup.toAddCommMonoid M inst_2) (@AddCommGroup.toAddCommMonoid M inst_2) inst_3 inst_3)
                  (@instMulZeroOneClassOfSemiring
                    (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                      (@RingHom.id R
                        (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                      M M (@AddCommGroup.toAddCommMonoid M inst_2) (@AddCommGroup.toAddCommMonoid M inst_2) inst_3 inst_3)
                    (@Module.End.instSemiring R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                      (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)))))
            rho g)
          (@LinearMap.id R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
            (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)

noncomputable def UpperTheory.Reformulated.B.CoboundaryOfGenerator.B1.{u_1, u_2, u_3} :
    {R : Type u_1} →
      [inst : CommRing R] →
        {G : Type u_2} →
          [inst_1 : Group G] →
            {M : Type u_3} →
              [inst_2 : AddCommGroup M] →
                [inst_3 :
                    @_root_.Module R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                      (@AddCommGroup.toAddCommMonoid M inst_2)] →
                  @Representation R G M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                      (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst_1)) (@AddCommGroup.toAddCommMonoid M inst_2)
                      inst_3 →
                    @Submodule R (G → M) (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                      (@Pi.addCommMonoid G (fun (a : G) ↦ M) fun (i : G) ↦ @AddCommGroup.toAddCommMonoid M inst_2)
                      (@Pi.Function.module G R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                        (@AddCommGroup.toAddCommMonoid M inst_2) inst_3) :=
    fun {R : Type u_1} [inst : CommRing R] {G : Type u_2} [inst_1 : Group G] {M : Type u_3} [inst_2 : AddCommGroup M]
        [inst_3 :
          @_root_.Module R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
            (@AddCommGroup.toAddCommMonoid M inst_2)]
        (rho :
          @Representation R G M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
            (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst_1)) (@AddCommGroup.toAddCommMonoid M inst_2) inst_3) ↦
      @LinearMap.range R R M (G → M) (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
        (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) (@AddCommGroup.toAddCommMonoid M inst_2)
        (@Pi.addCommMonoid G (fun (a : G) ↦ M) fun (i : G) ↦ @AddCommGroup.toAddCommMonoid M inst_2) inst_3
        (@Pi.Function.module G R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
          (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
        (@RingHom.id R (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
        (@UpperTheory.Reformulated.B.CoboundaryOfGenerator.aux7 R inst) (@UpperTheory.Reformulated.B.CoboundaryOfGenerator.d0 R inst G inst_1 M inst_2 inst_3 rho)

theorem UpperTheory.Reformulated.B.CoboundaryOfGenerator.cobOfGen :
    ∀ (l : Nat) [inst : Fact (Nat.Prime l)] (Γ : Type) [inst_1 : Group Γ] [inst_2 : TopologicalSpace Γ]
      [@IsTopologicalGroup Γ inst_2 inst_1] [@CompactSpace Γ inst_2]
      (χ :
        @MonoidHom Γ
          (@Units (@PadicInt l inst)
            (@Semiring.toMonoid (@PadicInt l inst)
              (@CommSemiring.toSemiring (@PadicInt l inst)
                (@CommRing.toCommSemiring (@PadicInt l inst) (@PadicInt.instCommRing l inst)))))
          (@MulOneClass.toMulOne Γ (@Monoid.toMulOneClass Γ (@DivInvMonoid.toMonoid Γ (@Group.toDivInvMonoid Γ inst_1))))
          (@MulOneClass.toMulOne
            (@Units (@PadicInt l inst)
              (@Semiring.toMonoid (@PadicInt l inst)
                (@CommSemiring.toSemiring (@PadicInt l inst)
                  (@CommRing.toCommSemiring (@PadicInt l inst) (@PadicInt.instCommRing l inst)))))
            (@Units.instMulOneClass (@PadicInt l inst)
              (@Semiring.toMonoid (@PadicInt l inst)
                (@CommSemiring.toSemiring (@PadicInt l inst)
                  (@CommRing.toCommSemiring (@PadicInt l inst) (@PadicInt.instCommRing l inst)))))))
      (R M : Type) [inst_5 : CommRing R] [inst_6 : AddCommGroup M]
      [inst_7 :
        @_root_.Module R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_5))
          (@AddCommGroup.toAddCommMonoid M inst_6)]
      [inst_8 : TopologicalSpace M] [inst_9 : @DiscreteTopology M inst_8]
      (ρ :
        @Representation R Γ M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_5))
          (@DivInvMonoid.toMonoid Γ (@Group.toDivInvMonoid Γ inst_1)) (@AddCommGroup.toAddCommMonoid M inst_6) inst_7)
      (γ : Γ),
      @Continuous Γ
          (@Units (@PadicInt l inst)
            (@Semiring.toMonoid (@PadicInt l inst)
              (@CommSemiring.toSemiring (@PadicInt l inst)
                (@CommRing.toCommSemiring (@PadicInt l inst) (@PadicInt.instCommRing l inst)))))
          inst_2
          (@Units.instTopologicalSpaceUnits (@PadicInt l inst)
            (@UniformSpace.toTopologicalSpace (@PadicInt l inst)
              (@PseudoMetricSpace.toUniformSpace (@PadicInt l inst)
                (@SeminormedRing.toPseudoMetricSpace (@PadicInt l inst)
                  (@SeminormedCommRing.toSeminormedRing (@PadicInt l inst)
                    (@NormedCommRing.toSeminormedCommRing (@PadicInt l inst) (@PadicInt.instNormedCommRing l inst))))))
            (@Semiring.toMonoid (@PadicInt l inst)
              (@CommSemiring.toSemiring (@PadicInt l inst)
                (@CommRing.toCommSemiring (@PadicInt l inst) (@PadicInt.instCommRing l inst)))))
          (@DFunLike.coe
            (@MonoidHom Γ
              (@Units (@PadicInt l inst)
                (@Semiring.toMonoid (@PadicInt l inst)
                  (@CommSemiring.toSemiring (@PadicInt l inst)
                    (@CommRing.toCommSemiring (@PadicInt l inst) (@PadicInt.instCommRing l inst)))))
              (@MulOneClass.toMulOne Γ
                (@Monoid.toMulOneClass Γ (@DivInvMonoid.toMonoid Γ (@Group.toDivInvMonoid Γ inst_1))))
              (@MulOneClass.toMulOne
                (@Units (@PadicInt l inst)
                  (@Semiring.toMonoid (@PadicInt l inst)
                    (@CommSemiring.toSemiring (@PadicInt l inst)
                      (@CommRing.toCommSemiring (@PadicInt l inst) (@PadicInt.instCommRing l inst)))))
                (@Units.instMulOneClass (@PadicInt l inst)
                  (@Semiring.toMonoid (@PadicInt l inst)
                    (@CommSemiring.toSemiring (@PadicInt l inst)
                      (@CommRing.toCommSemiring (@PadicInt l inst) (@PadicInt.instCommRing l inst)))))))
            Γ
            (fun (x : Γ) ↦
              @Units (@PadicInt l inst)
                (@Semiring.toMonoid (@PadicInt l inst)
                  (@CommSemiring.toSemiring (@PadicInt l inst)
                    (@CommRing.toCommSemiring (@PadicInt l inst) (@PadicInt.instCommRing l inst)))))
            (@MonoidHom.instFunLike Γ
              (@Units (@PadicInt l inst)
                (@Semiring.toMonoid (@PadicInt l inst)
                  (@CommSemiring.toSemiring (@PadicInt l inst)
                    (@CommRing.toCommSemiring (@PadicInt l inst) (@PadicInt.instCommRing l inst)))))
              (@MulOneClass.toMulOne Γ
                (@Monoid.toMulOneClass Γ (@DivInvMonoid.toMonoid Γ (@Group.toDivInvMonoid Γ inst_1))))
              (@MulOneClass.toMulOne
                (@Units (@PadicInt l inst)
                  (@Semiring.toMonoid (@PadicInt l inst)
                    (@CommSemiring.toSemiring (@PadicInt l inst)
                      (@CommRing.toCommSemiring (@PadicInt l inst) (@PadicInt.instCommRing l inst)))))
                (@Units.instMulOneClass (@PadicInt l inst)
                  (@Semiring.toMonoid (@PadicInt l inst)
                    (@CommSemiring.toSemiring (@PadicInt l inst)
                      (@CommRing.toCommSemiring (@PadicInt l inst) (@PadicInt.instCommRing l inst)))))))
            χ) →
        @UpperTheory.Reformulated.B.CoboundaryOfGenerator.ContAction R inst_5 Γ inst_1 inst_2 M inst_6 inst_7 inst_8 ρ →
          (∀ (g : Γ),
              @Eq
                  (@Units (@PadicInt l inst)
                    (@Semiring.toMonoid (@PadicInt l inst)
                      (@CommSemiring.toSemiring (@PadicInt l inst)
                        (@CommRing.toCommSemiring (@PadicInt l inst) (@PadicInt.instCommRing l inst)))))
                  (@DFunLike.coe
                    (@MonoidHom Γ
                      (@Units (@PadicInt l inst)
                        (@Semiring.toMonoid (@PadicInt l inst)
                          (@CommSemiring.toSemiring (@PadicInt l inst)
                            (@CommRing.toCommSemiring (@PadicInt l inst) (@PadicInt.instCommRing l inst)))))
                      (@MulOneClass.toMulOne Γ
                        (@Monoid.toMulOneClass Γ (@DivInvMonoid.toMonoid Γ (@Group.toDivInvMonoid Γ inst_1))))
                      (@MulOneClass.toMulOne
                        (@Units (@PadicInt l inst)
                          (@Semiring.toMonoid (@PadicInt l inst)
                            (@CommSemiring.toSemiring (@PadicInt l inst)
                              (@CommRing.toCommSemiring (@PadicInt l inst) (@PadicInt.instCommRing l inst)))))
                        (@Units.instMulOneClass (@PadicInt l inst)
                          (@Semiring.toMonoid (@PadicInt l inst)
                            (@CommSemiring.toSemiring (@PadicInt l inst)
                              (@CommRing.toCommSemiring (@PadicInt l inst) (@PadicInt.instCommRing l inst)))))))
                    Γ
                    (fun (x : Γ) ↦
                      @Units (@PadicInt l inst)
                        (@Semiring.toMonoid (@PadicInt l inst)
                          (@CommSemiring.toSemiring (@PadicInt l inst)
                            (@CommRing.toCommSemiring (@PadicInt l inst) (@PadicInt.instCommRing l inst)))))
                    (@MonoidHom.instFunLike Γ
                      (@Units (@PadicInt l inst)
                        (@Semiring.toMonoid (@PadicInt l inst)
                          (@CommSemiring.toSemiring (@PadicInt l inst)
                            (@CommRing.toCommSemiring (@PadicInt l inst) (@PadicInt.instCommRing l inst)))))
                      (@MulOneClass.toMulOne Γ
                        (@Monoid.toMulOneClass Γ (@DivInvMonoid.toMonoid Γ (@Group.toDivInvMonoid Γ inst_1))))
                      (@MulOneClass.toMulOne
                        (@Units (@PadicInt l inst)
                          (@Semiring.toMonoid (@PadicInt l inst)
                            (@CommSemiring.toSemiring (@PadicInt l inst)
                              (@CommRing.toCommSemiring (@PadicInt l inst) (@PadicInt.instCommRing l inst)))))
                        (@Units.instMulOneClass (@PadicInt l inst)
                          (@Semiring.toMonoid (@PadicInt l inst)
                            (@CommSemiring.toSemiring (@PadicInt l inst)
                              (@CommRing.toCommSemiring (@PadicInt l inst) (@PadicInt.instCommRing l inst)))))))
                    χ g)
                  (@OfNat.ofNat
                    (@Units (@PadicInt l inst)
                      (@Semiring.toMonoid (@PadicInt l inst)
                        (@CommSemiring.toSemiring (@PadicInt l inst)
                          (@CommRing.toCommSemiring (@PadicInt l inst) (@PadicInt.instCommRing l inst)))))
                    (nat_lit 1)
                    (@One.toOfNat1
                      (@Units (@PadicInt l inst)
                        (@Semiring.toMonoid (@PadicInt l inst)
                          (@CommSemiring.toSemiring (@PadicInt l inst)
                            (@CommRing.toCommSemiring (@PadicInt l inst) (@PadicInt.instCommRing l inst)))))
                      (@Units.instOne (@PadicInt l inst)
                        (@Semiring.toMonoid (@PadicInt l inst)
                          (@CommSemiring.toSemiring (@PadicInt l inst)
                            (@CommRing.toCommSemiring (@PadicInt l inst) (@PadicInt.instCommRing l inst))))))) →
                ∀ (m : M),
                  @Eq M
                    (@DFunLike.coe
                      (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_5))
                        (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_5))
                        (@RingHom.id R
                          (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_5))))
                        M M (@AddCommGroup.toAddCommMonoid M inst_6) (@AddCommGroup.toAddCommMonoid M inst_6) inst_7 inst_7)
                      M (fun (x : M) ↦ M)
                      (@LinearMap.instFunLike R R M M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_5))
                        (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_5))
                        (@AddCommGroup.toAddCommMonoid M inst_6) (@AddCommGroup.toAddCommMonoid M inst_6) inst_7 inst_7
                        (@RingHom.id R
                          (@Semiring.toNonAssocSemiring R
                            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_5)))))
                      (@DFunLike.coe
                        (@Representation R Γ M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_5))
                          (@DivInvMonoid.toMonoid Γ (@Group.toDivInvMonoid Γ inst_1))
                          (@AddCommGroup.toAddCommMonoid M inst_6) inst_7)
                        Γ
                        (fun (x : Γ) ↦
                          @LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_5))
                            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_5))
                            (@RingHom.id R
                              (@Semiring.toNonAssocSemiring R
                                (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_5))))
                            M M (@AddCommGroup.toAddCommMonoid M inst_6) (@AddCommGroup.toAddCommMonoid M inst_6) inst_7
                            inst_7)
                        (@MonoidHom.instFunLike Γ
                          (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_5))
                            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_5))
                            (@RingHom.id R
                              (@Semiring.toNonAssocSemiring R
                                (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_5))))
                            M M (@AddCommGroup.toAddCommMonoid M inst_6) (@AddCommGroup.toAddCommMonoid M inst_6) inst_7
                            inst_7)
                          (@MulOneClass.toMulOne Γ
                            (@Monoid.toMulOneClass Γ (@DivInvMonoid.toMonoid Γ (@Group.toDivInvMonoid Γ inst_1))))
                          (@MulOneClass.toMulOne
                            (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_5))
                              (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_5))
                              (@RingHom.id R
                                (@Semiring.toNonAssocSemiring R
                                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_5))))
                              M M (@AddCommGroup.toAddCommMonoid M inst_6) (@AddCommGroup.toAddCommMonoid M inst_6) inst_7
                              inst_7)
                            (@MulZeroOneClass.toMulOneClass
                              (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_5))
                                (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_5))
                                (@RingHom.id R
                                  (@Semiring.toNonAssocSemiring R
                                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_5))))
                                M M (@AddCommGroup.toAddCommMonoid M inst_6) (@AddCommGroup.toAddCommMonoid M inst_6) inst_7
                                inst_7)
                              (@instMulZeroOneClassOfSemiring
                                (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_5))
                                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_5))
                                  (@RingHom.id R
                                    (@Semiring.toNonAssocSemiring R
                                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_5))))
                                  M M (@AddCommGroup.toAddCommMonoid M inst_6) (@AddCommGroup.toAddCommMonoid M inst_6)
                                  inst_7 inst_7)
                                (@Module.End.instSemiring R M
                                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_5))
                                  (@AddCommGroup.toAddCommMonoid M inst_6) inst_7)))))
                        ρ g)
                      m)
                    m) →
            (∀ (g : Γ),
                @Membership.mem
                  (@Units (@PadicInt l inst)
                    (@Semiring.toMonoid (@PadicInt l inst)
                      (@CommSemiring.toSemiring (@PadicInt l inst)
                        (@CommRing.toCommSemiring (@PadicInt l inst) (@PadicInt.instCommRing l inst)))))
                  (@Subgroup
                    (@Units (@PadicInt l inst)
                      (@Semiring.toMonoid (@PadicInt l inst)
                        (@CommSemiring.toSemiring (@PadicInt l inst)
                          (@CommRing.toCommSemiring (@PadicInt l inst) (@PadicInt.instCommRing l inst)))))
                    (@Units.instGroup (@PadicInt l inst)
                      (@Semiring.toMonoid (@PadicInt l inst)
                        (@CommSemiring.toSemiring (@PadicInt l inst)
                          (@CommRing.toCommSemiring (@PadicInt l inst) (@PadicInt.instCommRing l inst))))))
                  (@SetLike.instMembership
                    (@Subgroup
                      (@Units (@PadicInt l inst)
                        (@Semiring.toMonoid (@PadicInt l inst)
                          (@CommSemiring.toSemiring (@PadicInt l inst)
                            (@CommRing.toCommSemiring (@PadicInt l inst) (@PadicInt.instCommRing l inst)))))
                      (@Units.instGroup (@PadicInt l inst)
                        (@Semiring.toMonoid (@PadicInt l inst)
                          (@CommSemiring.toSemiring (@PadicInt l inst)
                            (@CommRing.toCommSemiring (@PadicInt l inst) (@PadicInt.instCommRing l inst))))))
                    (@Units (@PadicInt l inst)
                      (@Semiring.toMonoid (@PadicInt l inst)
                        (@CommSemiring.toSemiring (@PadicInt l inst)
                          (@CommRing.toCommSemiring (@PadicInt l inst) (@PadicInt.instCommRing l inst)))))
                    (@Subgroup.instSetLike
                      (@Units (@PadicInt l inst)
                        (@Semiring.toMonoid (@PadicInt l inst)
                          (@CommSemiring.toSemiring (@PadicInt l inst)
                            (@CommRing.toCommSemiring (@PadicInt l inst) (@PadicInt.instCommRing l inst)))))
                      (@Units.instGroup (@PadicInt l inst)
                        (@Semiring.toMonoid (@PadicInt l inst)
                          (@CommSemiring.toSemiring (@PadicInt l inst)
                            (@CommRing.toCommSemiring (@PadicInt l inst) (@PadicInt.instCommRing l inst)))))))
                  (@Subgroup.topologicalClosure
                    (@Units (@PadicInt l inst)
                      (@Semiring.toMonoid (@PadicInt l inst)
                        (@CommSemiring.toSemiring (@PadicInt l inst)
                          (@CommRing.toCommSemiring (@PadicInt l inst) (@PadicInt.instCommRing l inst)))))
                    (@Units.instTopologicalSpaceUnits (@PadicInt l inst)
                      (@UniformSpace.toTopologicalSpace (@PadicInt l inst)
                        (@PseudoMetricSpace.toUniformSpace (@PadicInt l inst)
                          (@SeminormedRing.toPseudoMetricSpace (@PadicInt l inst)
                            (@SeminormedCommRing.toSeminormedRing (@PadicInt l inst)
                              (@NormedCommRing.toSeminormedCommRing (@PadicInt l inst)
                                (@PadicInt.instNormedCommRing l inst))))))
                      (@Semiring.toMonoid (@PadicInt l inst)
                        (@CommSemiring.toSemiring (@PadicInt l inst)
                          (@CommRing.toCommSemiring (@PadicInt l inst) (@PadicInt.instCommRing l inst)))))
                    (@Units.instGroup (@PadicInt l inst)
                      (@Semiring.toMonoid (@PadicInt l inst)
                        (@CommSemiring.toSemiring (@PadicInt l inst)
                          (@CommRing.toCommSemiring (@PadicInt l inst) (@PadicInt.instCommRing l inst)))))
                    (@Units.instIsTopologicalGroupOfContinuousMul (@PadicInt l inst)
                      (@Semiring.toMonoid (@PadicInt l inst)
                        (@CommSemiring.toSemiring (@PadicInt l inst)
                          (@CommRing.toCommSemiring (@PadicInt l inst) (@PadicInt.instCommRing l inst))))
                      (@UniformSpace.toTopologicalSpace (@PadicInt l inst)
                        (@PseudoMetricSpace.toUniformSpace (@PadicInt l inst)
                          (@SeminormedRing.toPseudoMetricSpace (@PadicInt l inst)
                            (@SeminormedCommRing.toSeminormedRing (@PadicInt l inst)
                              (@NormedCommRing.toSeminormedCommRing (@PadicInt l inst)
                                (@PadicInt.instNormedCommRing l inst))))))
                      (@IsTopologicalSemiring.toContinuousMul (@PadicInt l inst)
                        (@UniformSpace.toTopologicalSpace (@PadicInt l inst)
                          (@PseudoMetricSpace.toUniformSpace (@PadicInt l inst)
                            (@SeminormedRing.toPseudoMetricSpace (@PadicInt l inst)
                              (@SeminormedCommRing.toSeminormedRing (@PadicInt l inst)
                                (@NormedCommRing.toSeminormedCommRing (@PadicInt l inst)
                                  (@PadicInt.instNormedCommRing l inst))))))
                        (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring (@PadicInt l inst)
                          (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing (@PadicInt l inst)
                            (@NonUnitalCommRing.toNonUnitalNonAssocCommRing (@PadicInt l inst)
                              (@CommRing.toNonUnitalCommRing (@PadicInt l inst) (@PadicInt.instCommRing l inst)))))
                        (@IsTopologicalRing.toIsTopologicalSemiring (@PadicInt l inst)
                          (@UniformSpace.toTopologicalSpace (@PadicInt l inst)
                            (@PseudoMetricSpace.toUniformSpace (@PadicInt l inst)
                              (@SeminormedRing.toPseudoMetricSpace (@PadicInt l inst)
                                (@SeminormedCommRing.toSeminormedRing (@PadicInt l inst)
                                  (@NormedCommRing.toSeminormedCommRing (@PadicInt l inst)
                                    (@PadicInt.instNormedCommRing l inst))))))
                          (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing (@PadicInt l inst)
                            (@NonUnitalCommRing.toNonUnitalNonAssocCommRing (@PadicInt l inst)
                              (@CommRing.toNonUnitalCommRing (@PadicInt l inst) (@PadicInt.instCommRing l inst))))
                          (@NonUnitalSeminormedRing.toIsTopologicalRing (@PadicInt l inst)
                            (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing (@PadicInt l inst)
                              (@SeminormedCommRing.toNonUnitalSeminormedCommRing (@PadicInt l inst)
                                (@NormedCommRing.toSeminormedCommRing (@PadicInt l inst)
                                  (@PadicInt.instNormedCommRing l inst))))))))
                    (@Subgroup.zpowers
                      (@Units (@PadicInt l inst)
                        (@Semiring.toMonoid (@PadicInt l inst)
                          (@CommSemiring.toSemiring (@PadicInt l inst)
                            (@CommRing.toCommSemiring (@PadicInt l inst) (@PadicInt.instCommRing l inst)))))
                      (@Units.instGroup (@PadicInt l inst)
                        (@Semiring.toMonoid (@PadicInt l inst)
                          (@CommSemiring.toSemiring (@PadicInt l inst)
                            (@CommRing.toCommSemiring (@PadicInt l inst) (@PadicInt.instCommRing l inst)))))
                      (@DFunLike.coe
                        (@MonoidHom Γ
                          (@Units (@PadicInt l inst)
                            (@Semiring.toMonoid (@PadicInt l inst)
                              (@CommSemiring.toSemiring (@PadicInt l inst)
                                (@CommRing.toCommSemiring (@PadicInt l inst) (@PadicInt.instCommRing l inst)))))
                          (@MulOneClass.toMulOne Γ
                            (@Monoid.toMulOneClass Γ (@DivInvMonoid.toMonoid Γ (@Group.toDivInvMonoid Γ inst_1))))
                          (@MulOneClass.toMulOne
                            (@Units (@PadicInt l inst)
                              (@Semiring.toMonoid (@PadicInt l inst)
                                (@CommSemiring.toSemiring (@PadicInt l inst)
                                  (@CommRing.toCommSemiring (@PadicInt l inst) (@PadicInt.instCommRing l inst)))))
                            (@Units.instMulOneClass (@PadicInt l inst)
                              (@Semiring.toMonoid (@PadicInt l inst)
                                (@CommSemiring.toSemiring (@PadicInt l inst)
                                  (@CommRing.toCommSemiring (@PadicInt l inst) (@PadicInt.instCommRing l inst)))))))
                        Γ
                        (fun (x : Γ) ↦
                          @Units (@PadicInt l inst)
                            (@Semiring.toMonoid (@PadicInt l inst)
                              (@CommSemiring.toSemiring (@PadicInt l inst)
                                (@CommRing.toCommSemiring (@PadicInt l inst) (@PadicInt.instCommRing l inst)))))
                        (@MonoidHom.instFunLike Γ
                          (@Units (@PadicInt l inst)
                            (@Semiring.toMonoid (@PadicInt l inst)
                              (@CommSemiring.toSemiring (@PadicInt l inst)
                                (@CommRing.toCommSemiring (@PadicInt l inst) (@PadicInt.instCommRing l inst)))))
                          (@MulOneClass.toMulOne Γ
                            (@Monoid.toMulOneClass Γ (@DivInvMonoid.toMonoid Γ (@Group.toDivInvMonoid Γ inst_1))))
                          (@MulOneClass.toMulOne
                            (@Units (@PadicInt l inst)
                              (@Semiring.toMonoid (@PadicInt l inst)
                                (@CommSemiring.toSemiring (@PadicInt l inst)
                                  (@CommRing.toCommSemiring (@PadicInt l inst) (@PadicInt.instCommRing l inst)))))
                            (@Units.instMulOneClass (@PadicInt l inst)
                              (@Semiring.toMonoid (@PadicInt l inst)
                                (@CommSemiring.toSemiring (@PadicInt l inst)
                                  (@CommRing.toCommSemiring (@PadicInt l inst) (@PadicInt.instCommRing l inst)))))))
                        χ γ)))
                  (@DFunLike.coe
                    (@MonoidHom Γ
                      (@Units (@PadicInt l inst)
                        (@Semiring.toMonoid (@PadicInt l inst)
                          (@CommSemiring.toSemiring (@PadicInt l inst)
                            (@CommRing.toCommSemiring (@PadicInt l inst) (@PadicInt.instCommRing l inst)))))
                      (@MulOneClass.toMulOne Γ
                        (@Monoid.toMulOneClass Γ (@DivInvMonoid.toMonoid Γ (@Group.toDivInvMonoid Γ inst_1))))
                      (@MulOneClass.toMulOne
                        (@Units (@PadicInt l inst)
                          (@Semiring.toMonoid (@PadicInt l inst)
                            (@CommSemiring.toSemiring (@PadicInt l inst)
                              (@CommRing.toCommSemiring (@PadicInt l inst) (@PadicInt.instCommRing l inst)))))
                        (@Units.instMulOneClass (@PadicInt l inst)
                          (@Semiring.toMonoid (@PadicInt l inst)
                            (@CommSemiring.toSemiring (@PadicInt l inst)
                              (@CommRing.toCommSemiring (@PadicInt l inst) (@PadicInt.instCommRing l inst)))))))
                    Γ
                    (fun (x : Γ) ↦
                      @Units (@PadicInt l inst)
                        (@Semiring.toMonoid (@PadicInt l inst)
                          (@CommSemiring.toSemiring (@PadicInt l inst)
                            (@CommRing.toCommSemiring (@PadicInt l inst) (@PadicInt.instCommRing l inst)))))
                    (@MonoidHom.instFunLike Γ
                      (@Units (@PadicInt l inst)
                        (@Semiring.toMonoid (@PadicInt l inst)
                          (@CommSemiring.toSemiring (@PadicInt l inst)
                            (@CommRing.toCommSemiring (@PadicInt l inst) (@PadicInt.instCommRing l inst)))))
                      (@MulOneClass.toMulOne Γ
                        (@Monoid.toMulOneClass Γ (@DivInvMonoid.toMonoid Γ (@Group.toDivInvMonoid Γ inst_1))))
                      (@MulOneClass.toMulOne
                        (@Units (@PadicInt l inst)
                          (@Semiring.toMonoid (@PadicInt l inst)
                            (@CommSemiring.toSemiring (@PadicInt l inst)
                              (@CommRing.toCommSemiring (@PadicInt l inst) (@PadicInt.instCommRing l inst)))))
                        (@Units.instMulOneClass (@PadicInt l inst)
                          (@Semiring.toMonoid (@PadicInt l inst)
                            (@CommSemiring.toSemiring (@PadicInt l inst)
                              (@CommRing.toCommSemiring (@PadicInt l inst) (@PadicInt.instCommRing l inst)))))))
                    χ g)) →
              (@Function.Surjective M M fun (m : M) ↦
                  @HSub.hSub M M M
                    (@instHSub M (@SubNegMonoid.toSub M (@AddGroup.toSubNegMonoid M (@AddCommGroup.toAddGroup M inst_6))))
                    (@DFunLike.coe
                      (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_5))
                        (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_5))
                        (@RingHom.id R
                          (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_5))))
                        M M (@AddCommGroup.toAddCommMonoid M inst_6) (@AddCommGroup.toAddCommMonoid M inst_6) inst_7 inst_7)
                      M (fun (x : M) ↦ M)
                      (@LinearMap.instFunLike R R M M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_5))
                        (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_5))
                        (@AddCommGroup.toAddCommMonoid M inst_6) (@AddCommGroup.toAddCommMonoid M inst_6) inst_7 inst_7
                        (@RingHom.id R
                          (@Semiring.toNonAssocSemiring R
                            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_5)))))
                      (@DFunLike.coe
                        (@Representation R Γ M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_5))
                          (@DivInvMonoid.toMonoid Γ (@Group.toDivInvMonoid Γ inst_1))
                          (@AddCommGroup.toAddCommMonoid M inst_6) inst_7)
                        Γ
                        (fun (x : Γ) ↦
                          @LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_5))
                            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_5))
                            (@RingHom.id R
                              (@Semiring.toNonAssocSemiring R
                                (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_5))))
                            M M (@AddCommGroup.toAddCommMonoid M inst_6) (@AddCommGroup.toAddCommMonoid M inst_6) inst_7
                            inst_7)
                        (@MonoidHom.instFunLike Γ
                          (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_5))
                            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_5))
                            (@RingHom.id R
                              (@Semiring.toNonAssocSemiring R
                                (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_5))))
                            M M (@AddCommGroup.toAddCommMonoid M inst_6) (@AddCommGroup.toAddCommMonoid M inst_6) inst_7
                            inst_7)
                          (@MulOneClass.toMulOne Γ
                            (@Monoid.toMulOneClass Γ (@DivInvMonoid.toMonoid Γ (@Group.toDivInvMonoid Γ inst_1))))
                          (@MulOneClass.toMulOne
                            (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_5))
                              (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_5))
                              (@RingHom.id R
                                (@Semiring.toNonAssocSemiring R
                                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_5))))
                              M M (@AddCommGroup.toAddCommMonoid M inst_6) (@AddCommGroup.toAddCommMonoid M inst_6) inst_7
                              inst_7)
                            (@MulZeroOneClass.toMulOneClass
                              (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_5))
                                (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_5))
                                (@RingHom.id R
                                  (@Semiring.toNonAssocSemiring R
                                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_5))))
                                M M (@AddCommGroup.toAddCommMonoid M inst_6) (@AddCommGroup.toAddCommMonoid M inst_6) inst_7
                                inst_7)
                              (@instMulZeroOneClassOfSemiring
                                (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_5))
                                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_5))
                                  (@RingHom.id R
                                    (@Semiring.toNonAssocSemiring R
                                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_5))))
                                  M M (@AddCommGroup.toAddCommMonoid M inst_6) (@AddCommGroup.toAddCommMonoid M inst_6)
                                  inst_7 inst_7)
                                (@Module.End.instSemiring R M
                                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_5))
                                  (@AddCommGroup.toAddCommMonoid M inst_6) inst_7)))))
                        ρ γ)
                      m)
                    m) →
                ∀ (z : Γ → M),
                  @Membership.mem (Γ → M)
                      (@Submodule R (Γ → M) (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_5))
                        (@Pi.addCommMonoid Γ (fun (a : Γ) ↦ M) fun (i : Γ) ↦ @AddCommGroup.toAddCommMonoid M inst_6)
                        (@Pi.Function.module Γ R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_5))
                          (@AddCommGroup.toAddCommMonoid M inst_6) inst_7))
                      (@SetLike.instMembership
                        (@Submodule R (Γ → M) (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_5))
                          (@Pi.addCommMonoid Γ (fun (a : Γ) ↦ M) fun (i : Γ) ↦ @AddCommGroup.toAddCommMonoid M inst_6)
                          (@Pi.Function.module Γ R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_5))
                            (@AddCommGroup.toAddCommMonoid M inst_6) inst_7))
                        (Γ → M)
                        (@Submodule.setLike R (Γ → M) (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_5))
                          (@Pi.addCommMonoid Γ (fun (a : Γ) ↦ M) fun (i : Γ) ↦ @AddCommGroup.toAddCommMonoid M inst_6)
                          (@Pi.Function.module Γ R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_5))
                            (@AddCommGroup.toAddCommMonoid M inst_6) inst_7)))
                      (@UpperTheory.Reformulated.B.CoboundaryOfGenerator.Z1 R inst_5 Γ inst_1 inst_2 M inst_6 inst_7 inst_8
                        (@topologicalAddGroup_of_discreteTopology M inst_8 (@AddCommGroup.toAddGroup M inst_6) inst_9)
                        (@UpperTheory.Reformulated.B.CoboundaryOfGenerator.aux6 R M
                          (@SMulZeroClass.toSMul R M
                            (@AddZero.toZero M
                              (@AddZeroClass.toAddZero M
                                (@AddMonoid.toAddZeroClass M
                                  (@SubNegMonoid.toAddMonoid M
                                    (@AddGroup.toSubNegMonoid M (@AddCommGroup.toAddGroup M inst_6))))))
                            (@DistribSMul.toSMulZeroClass R M
                              (@AddMonoid.toAddZeroClass M
                                (@SubNegMonoid.toAddMonoid M
                                  (@AddGroup.toSubNegMonoid M (@AddCommGroup.toAddGroup M inst_6))))
                              (@DistribMulAction.toDistribSMul R M
                                (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_5)))
                                (@SubNegMonoid.toAddMonoid M
                                  (@AddGroup.toSubNegMonoid M (@AddCommGroup.toAddGroup M inst_6)))
                                (@Module.toDistribMulAction R M
                                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_5))
                                  (@AddCommGroup.toAddCommMonoid M inst_6) inst_7))))
                          inst_8 inst_9)
                        ρ)
                      z →
                    (∀ (g : Γ),
                        @Eq
                            (@Units (@PadicInt l inst)
                              (@Semiring.toMonoid (@PadicInt l inst)
                                (@CommSemiring.toSemiring (@PadicInt l inst)
                                  (@CommRing.toCommSemiring (@PadicInt l inst) (@PadicInt.instCommRing l inst)))))
                            (@DFunLike.coe
                              (@MonoidHom Γ
                                (@Units (@PadicInt l inst)
                                  (@Semiring.toMonoid (@PadicInt l inst)
                                    (@CommSemiring.toSemiring (@PadicInt l inst)
                                      (@CommRing.toCommSemiring (@PadicInt l inst) (@PadicInt.instCommRing l inst)))))
                                (@MulOneClass.toMulOne Γ
                                  (@Monoid.toMulOneClass Γ (@DivInvMonoid.toMonoid Γ (@Group.toDivInvMonoid Γ inst_1))))
                                (@MulOneClass.toMulOne
                                  (@Units (@PadicInt l inst)
                                    (@Semiring.toMonoid (@PadicInt l inst)
                                      (@CommSemiring.toSemiring (@PadicInt l inst)
                                        (@CommRing.toCommSemiring (@PadicInt l inst) (@PadicInt.instCommRing l inst)))))
                                  (@Units.instMulOneClass (@PadicInt l inst)
                                    (@Semiring.toMonoid (@PadicInt l inst)
                                      (@CommSemiring.toSemiring (@PadicInt l inst)
                                        (@CommRing.toCommSemiring (@PadicInt l inst) (@PadicInt.instCommRing l inst)))))))
                              Γ
                              (fun (x : Γ) ↦
                                @Units (@PadicInt l inst)
                                  (@Semiring.toMonoid (@PadicInt l inst)
                                    (@CommSemiring.toSemiring (@PadicInt l inst)
                                      (@CommRing.toCommSemiring (@PadicInt l inst) (@PadicInt.instCommRing l inst)))))
                              (@MonoidHom.instFunLike Γ
                                (@Units (@PadicInt l inst)
                                  (@Semiring.toMonoid (@PadicInt l inst)
                                    (@CommSemiring.toSemiring (@PadicInt l inst)
                                      (@CommRing.toCommSemiring (@PadicInt l inst) (@PadicInt.instCommRing l inst)))))
                                (@MulOneClass.toMulOne Γ
                                  (@Monoid.toMulOneClass Γ (@DivInvMonoid.toMonoid Γ (@Group.toDivInvMonoid Γ inst_1))))
                                (@MulOneClass.toMulOne
                                  (@Units (@PadicInt l inst)
                                    (@Semiring.toMonoid (@PadicInt l inst)
                                      (@CommSemiring.toSemiring (@PadicInt l inst)
                                        (@CommRing.toCommSemiring (@PadicInt l inst) (@PadicInt.instCommRing l inst)))))
                                  (@Units.instMulOneClass (@PadicInt l inst)
                                    (@Semiring.toMonoid (@PadicInt l inst)
                                      (@CommSemiring.toSemiring (@PadicInt l inst)
                                        (@CommRing.toCommSemiring (@PadicInt l inst) (@PadicInt.instCommRing l inst)))))))
                              χ g)
                            (@OfNat.ofNat
                              (@Units (@PadicInt l inst)
                                (@Semiring.toMonoid (@PadicInt l inst)
                                  (@CommSemiring.toSemiring (@PadicInt l inst)
                                    (@CommRing.toCommSemiring (@PadicInt l inst) (@PadicInt.instCommRing l inst)))))
                              (nat_lit 1)
                              (@One.toOfNat1
                                (@Units (@PadicInt l inst)
                                  (@Semiring.toMonoid (@PadicInt l inst)
                                    (@CommSemiring.toSemiring (@PadicInt l inst)
                                      (@CommRing.toCommSemiring (@PadicInt l inst) (@PadicInt.instCommRing l inst)))))
                                (@Units.instOne (@PadicInt l inst)
                                  (@Semiring.toMonoid (@PadicInt l inst)
                                    (@CommSemiring.toSemiring (@PadicInt l inst)
                                      (@CommRing.toCommSemiring (@PadicInt l inst) (@PadicInt.instCommRing l inst))))))) →
                          @Eq M (z g)
                            (@OfNat.ofNat M (nat_lit 0)
                              (@Zero.toOfNat0 M
                                (@NegZeroClass.toZero M
                                  (@SubNegZeroMonoid.toNegZeroClass M
                                    (@SubtractionMonoid.toSubNegZeroMonoid M
                                      (@SubtractionCommMonoid.toSubtractionMonoid M
                                        (@AddCommGroup.toDivisionAddCommMonoid M inst_6)))))))) →
                      @Membership.mem (Γ → M)
                        (@Submodule R (Γ → M) (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_5))
                          (@Pi.addCommMonoid Γ (fun (a : Γ) ↦ M) fun (i : Γ) ↦ @AddCommGroup.toAddCommMonoid M inst_6)
                          (@Pi.Function.module Γ R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_5))
                            (@AddCommGroup.toAddCommMonoid M inst_6) inst_7))
                        (@SetLike.instMembership
                          (@Submodule R (Γ → M) (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_5))
                            (@Pi.addCommMonoid Γ (fun (a : Γ) ↦ M) fun (i : Γ) ↦ @AddCommGroup.toAddCommMonoid M inst_6)
                            (@Pi.Function.module Γ R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_5))
                              (@AddCommGroup.toAddCommMonoid M inst_6) inst_7))
                          (Γ → M)
                          (@Submodule.setLike R (Γ → M) (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_5))
                            (@Pi.addCommMonoid Γ (fun (a : Γ) ↦ M) fun (i : Γ) ↦ @AddCommGroup.toAddCommMonoid M inst_6)
                            (@Pi.Function.module Γ R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_5))
                              (@AddCommGroup.toAddCommMonoid M inst_6) inst_7)))
                        (@UpperTheory.Reformulated.B.CoboundaryOfGenerator.B1 R inst_5 Γ inst_1 M inst_6 inst_7 ρ) z := by
  intro l _ Γ _ _ _ _ χ R M _ _ _ _ _ ρ γ hχ hρ hker hgen hsurj z hz hz0
  have hzc : Continuous z := hz.1
  have hzm : ∀ g h : Γ, z (g * h) = z g + ρ g (z h) := hz.2
  obtain ⟨m, hm⟩ := hsurj (z γ)
  have hm' : ρ γ m - m = z γ := hm
  have hone : z 1 = 0 := hz0 1 (map_one χ)
  let S : Subgroup Γ :=
    { carrier := {g | z g = ρ g m - m}
      one_mem' := by
        change z 1 = ρ 1 m - m
        simp [hone]
      mul_mem' := by
        intro a b ha hb
        have ha' : z a = ρ a m - m := ha
        have hb' : z b = ρ b m - m := hb
        change z (a * b) = ρ (a * b) m - m
        rw [hzm, ha', hb', map_mul, map_sub, Module.End.mul_apply]
        abel
      inv_mem' := by
        intro a ha
        have ha' : z a = ρ a m - m := ha
        change z a⁻¹ = ρ a⁻¹ m - m
        have h1 := hzm a⁻¹ a
        have h2 : ρ a⁻¹ (ρ a m) = m := by
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
        rw [inv_mul_cancel, hone, ha', map_sub, h2] at h1
        rw [eq_neg_of_add_eq_zero_left h1.symm, neg_sub] }
  have hρm : Continuous fun g : Γ => ρ g m :=
    Continuous.comp (g := fun p : Γ × M => ρ p.1 p.2) (f := fun g : Γ => (g, m)) hρ
      (continuous_id.prodMk continuous_const)
  have hSc : IsClosed (S : Set Γ) := isClosed_eq hzc (hρm.sub continuous_const)
  have himg : IsClosed ((S.map χ : Subgroup ℤ_[l]ˣ) : Set ℤ_[l]ˣ) := by
    rw [Subgroup.coe_map]
    exact (hSc.isCompact.image hχ).isClosed
  have hle : (Subgroup.zpowers (χ γ)).topologicalClosure ≤ S.map χ :=
    Subgroup.topologicalClosure_minimal _
      ((Subgroup.zpowers_le).2 ⟨γ, hm'.symm, rfl⟩) himg
  have hall : ∀ g : Γ, g ∈ S := by
    intro g
    obtain ⟨s, hs, hsg⟩ := hle (hgen g)
    have hk : χ (s⁻¹ * g) = 1 := by rw [map_mul, map_inv, hsg, inv_mul_cancel]
    have hmem : s⁻¹ * g ∈ S := by
      change z (s⁻¹ * g) = ρ (s⁻¹ * g) m - m
      rw [hz0 _ hk, hker _ hk, sub_self]
    simpa using S.mul_mem hs hmem
  refine ⟨m, funext fun g => ?_⟩
  exact (hall g).symm
